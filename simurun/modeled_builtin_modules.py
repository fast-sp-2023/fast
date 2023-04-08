from .graph import Graph
from .utilities import NodeHandleResult, BranchTag, BranchTagContainer
from .utilities import wildcard
from .utilities import get_random_hex
from . import opgen
from .helpers import val_to_str
from .helpers2 import to_obj_nodes, to_values
from .helpers2 import add_contributes_to
import sty
import re
import os
from .logger import *
from itertools import chain


logger = create_logger("main_logger", output_type="file")


def get_module(G, name):
    if name in modeled_modules:
        if name in G.builtin_modules:
            return G.builtin_modules[name]
        else:
            logger.log(ATTENTION, 'Setting up built-in module {}...'
                .format(name))
            module_exports = modeled_modules[name](G)
            G.builtin_modules[name] = module_exports
            return module_exports
    else:
        return None


def setup_fs(G: Graph):
    module_exports = G.add_obj_node()
    G.add_blank_func_as_prop('readFile', module_exports, read_file)
    G.add_blank_func_as_prop('readFileSync', module_exports, read_file_sync)
    return module_exports


def read_file(G: Graph, caller_ast, extra, _, path=NodeHandleResult(),
    options=None, callback=NodeHandleResult()):
    data = read_file_sync(G, caller_ast, extra, None, path, options)
    opgen.call_function(G, callback.obj_nodes,
        args=[NodeHandleResult(obj_nodes=[G.null_obj]), data],
        extra=extra)
    return NodeHandleResult()


def read_file_sync(G: Graph, caller_ast, extra, _, path=NodeHandleResult(),
    options=None):
    paths = list(filter(lambda x: x is not None, path.values))
    for obj in path.obj_nodes:
        value = G.get_node_attr(obj).get('code')
        if value is not None:
            paths.append(value)
    returned_values = []
    returned_objs = []
    used_objs = path.obj_nodes + list(chain(*path.value_sources))
    # TODO: missing obj-level data flows
    for path in paths:
        if path == wildcard:
            returned_objs.append(G.add_obj_node(caller_ast, 'string', wildcard))
            continue
        abs_path = os.path.normpath(os.path.join(
                            G.get_cur_file_path(), '..', str(path)))
        if not os.path.exists(abs_path):
            logger.debug(f'Read file {path}, file does not exist')
            continue
        try:
            f = open(abs_path, 'r')
            content = f.read()
            f.close()
            returned_values.append(content)
            returned_objs.append(G.add_obj_node(caller_ast, 'string', content))
            logger.debug(f'Read file {path}, content: ' + re.sub(r'\n|\t', '',
                content))
        except Exception as e:
            logger.error(f'Read file {path} failed: {str(e)}')
    # return NodeHandleResult(values=returned_values) # TODO: move to values
    return NodeHandleResult(obj_nodes=returned_objs, used_objs=used_objs)


def setup_util(G: Graph):
    module_exports = G.add_obj_node()
    # G.add_blank_func_as_prop('promisify', module_exports, util_promisify)
    G.add_blank_func_as_prop('format', module_exports, util_format)
    return module_exports


def util_promisify(G: Graph, caller_ast, extra, _, func=NodeHandleResult()):
    returned_objs = []
    func_objs = to_obj_nodes(G, func, caller_ast)
    for func_obj in func_objs:
        def gen_func(func_obj):
            def returned_func(G: Graph, caller_ast, extra, this, *args):
                def executor(G: Graph, caller_ast, extra, this, on_fulfilled=NodeHandleResult(), on_rejected=NodeHandleResult()):
                    result, _ = opgen.call_function(G, [func_obj], args, this, extra, caller_ast)
                    opgen.call_function(G, to_obj_nodes(G, on_fulfilled, caller_ast),
                        args=[result], this=NodeHandleResult(), extra=extra, call_ast=caller_ast)
                executor_obj = G.add_blank_func_with_og_nodes('executor')
                G.set_node_attr(executor_obj, ('pythonfunc', executor))
                # too complicated:
                # _, promise = opgen.call_function(G, [G.promise_cons], [NodeHandleResult(obj_nodes=[executor])],
                #     extra=extra, caller_ast=caller_ast)
                
                # implement Promise constructor by yourself:
                promise = G.add_obj_node(caller_ast, None, None)
                G.add_obj_as_prop('__proto__', )
                G.set_node_attr(promise, ('executors', to_obj_nodes(G, executor, caller_ast)))
        new_func_obj = G.add_blank_func_with_og_nodes('promisified')
        G.set_node_attr(new_func_obj, ('pythonfunc', gen_func(func_obj)))
    return NodeHandleResult()


def util_format(G: Graph, caller_ast, extra, _, fmt=NodeHandleResult(), *args):
    returned_objs = []
    used_objs = set()
    args_obj_nodes = list(map(
        lambda arg: to_obj_nodes(G, arg, caller_ast), args))
    _space_obj = None
    def space_obj():
        nonlocal _space_obj
        if _space_obj is None:
            _space_obj = G.add_obj_node(None, 'string', ' ')
    for fmt_obj in to_obj_nodes(G, fmt, caller_ast):
        _format = G.get_node_attr(fmt_obj).get('code')
        if _format is None or _format == wildcard or type(_format) != str:
            def dfs1(i, buffer, sources):
                nonlocal G, args, returned_objs, used_objs
                if i >= len(args):
                    result_obj = G.add_obj_node(caller_ast, 'string', buffer)
                    opgen.add_contributes_to(G, sources, result_obj,
                                             operation='string_concat')
                    returned_objs.append(result_obj)
                    used_objs.update(sources)
                    return
                if i < len(args):
                    objs = args_obj_nodes[i] # TODO: verify if this is correct
                else:
                    objs = []
                for obj in objs:
                    value = val_to_str(G.get_node_attr(obj).get('code'))
                    if buffer == wildcard or value == wildcard:
                        dfs1(i + 1, wildcard, sources + [obj])
                    else:
                        dfs1(i + 1, buffer + value,
                             sources + [space_obj(), obj])
            dfs1(0, "", [])
        else:
            _f = re.split('(%.)', _format)
            _s = []
            for p in _f: # convert format string parts into obj nodes
                if p == '%%':
                    _s.append(G.add_obj_node(caller_ast, 'string', '%'))
                else: # others as is
                    _s.append(G.add_obj_node(caller_ast, 'string', p))
            def dfs2(i, buffer, sources):
                nonlocal G, args, returned_objs, used_objs, _f
                if i >= len(_f) and i >= len(args):
                    result_obj = G.add_obj_node(caller_ast, 'string', buffer)
                    opgen.add_contributes_to(G, sources, result_obj,
                                             operation='string_concat')
                    returned_objs.append(result_obj)
                    used_objs.update(sources)
                    return
                objs = None
                if i < len(args):
                    objs = args_obj_nodes[i] # TODO: verify if this is correct
                if i >= len(_f): # more arguments than specifiers
                    for obj in objs:
                        value = val_to_str(G.get_node_attr(obj).get('code'))
                        if buffer == wildcard or value == wildcard:
                            dfs2(i + 1, wildcard, sources + [obj])
                        else:
                            dfs2(i + 1, buffer + ' ' + value,
                                        sources + [space_obj(), obj])
                elif _f[i] == '%%':
                    if buffer == wildcard:
                        dfs2(i + 1, wildcard, sources + [_s[i]])
                    else:
                        dfs2(i + 1, buffer + '%', sources + [_s[i]])
                elif not _f[i].startswith('%') or i >= len(args):
                    # literal part or more specifiers than arguments
                    if buffer == wildcard:
                        dfs2(i + 1, wildcard, sources + [_s[i]])
                    else:
                        dfs2(i + 1, buffer + _f[i], sources + [_s[i]])
                else: # acutal format specifier
                    objs = args_obj_nodes[i]
                    for obj in objs:
                        value = val_to_str(G.get_node_attr(obj).get('code'))
                        if buffer == wildcard or value == wildcard:
                            dfs2(i + 1, wildcard, sources + [obj])
                        else:
                            dfs2(i + 1, buffer + value, sources + [obj])
            dfs2(0, "", [])
    return NodeHandleResult(obj_nodes=returned_objs, used_objs=list(used_objs))


def setup_path(G: Graph):
    module_exports = G.add_obj_node()
    G.add_blank_func_as_prop('join', module_exports, path_join)
    return module_exports


def path_join(G: Graph, caller_ast, extra, _, *paths):
    returned_objects = []
    def dfs(i=0, buffer="", src=[]):
        nonlocal G, paths
        if i == len(paths):
            result = G.add_obj_node(caller_ast, 'string', buffer)
            returned_objects.append(result)
            random = get_random_hex()
            for j, s in enumerate(src):
                add_contributes_to(G, s, result, 'string_concat', j, random)
            return
        values, sources, _ = to_values(G, paths[i])
        for value, source in zip(values, sources):
            if value == wildcard or buffer == wildcard:
                dfs(i+1, wildcard, src + [source])
            else:
                if i == 0:
                    dfs(i+1, value, src + [source])
                else:
                    dfs(i+1, buffer + '/' + value, src + [source])
    dfs()
    used_objects = set()
    for path in paths:
        used_objects.update(path.obj_nodes)
    return NodeHandleResult(obj_nodes=returned_objects, used_objects=used_objects)


modeled_modules = {
    'fs': setup_fs,
    'util': setup_util,
    'path': setup_path
}
