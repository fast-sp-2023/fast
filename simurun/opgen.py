from .graph import Graph
from .utilities import NodeHandleResult, ExtraInfo
from .utilities import BranchTag, BranchTagContainer, get_random_hex
import os
import sys
import sty
import json
import re
import traceback as tb
from .logger import *
from . import modeled_js_builtins, modeled_builtin_modules
from .helpers import val_to_str, val_to_float, is_int
from .helpers import js_cmp, wildcard, undefined, is_wildcard_obj
from .helpers2 import *
from .esprima import esprima_parse, esprima_search
from . import solver
from itertools import chain, islice
from collections import defaultdict
from .trace_rule import TraceRule
from .vul_checking import *
from func_timeout import func_timeout, FunctionTimedOut
import time
from typing import Tuple
import hashlib

registered_func = {}

logger = create_logger("main_logger", output_type="file")
eval_logger = create_logger("eval_logger", output_type="file", file_name="evaluation.ndjson")

def get_argids_from_funcallee(G, node_id):
    """
    given a func node id, return a list of para ids
    """
    paras = []
    nodes = G.get_successors(node_id)
    for node in nodes:
        if G.get_node_attr(node)['type'] == 'AST_PARAM_LIST':
            params_id = list(G.get_successors(node))
            for i in range(len(params_id)):
                paras.append(0)
            for param_id in params_id:
                # only on child node
                para_num = int(G.get_node_attr(param_id)['childnum:int'])
                paras[para_num] = param_id 

    return paras

def get_argnames_from_funcaller(G, node_id):
    """
    given a func node id, return a list of para ids
    """
    paras = []
    nodes = G.get_successors(node_id)
    for node in nodes:
        if node == None:
            continue
        if G.get_node_attr(node).get('type') == 'AST_ARG_LIST':
            params_id = list(G.get_successors(node))
            for i in range(len(params_id)):
                paras.append(0)
            for param_id in params_id:
                # only on child node
                try:
                    para_num = int(G.get_node_attr(param_id)['childnum:int'])
                    sub_param_id = list(G.get_successors(param_id))[0]
                    paras[para_num] = G.get_node_attr(sub_param_id)['code']
                except:
                    pass
    return paras

def add_edges_between_funcs(G):
    """
    Deprecated

    we need to add CFG and DF edges between funcs
    find callers, if no flow to this node, go upper to find 
    a flow to. add CFG edges to callee CFG_ENTRY an DF edges
    to PARAS
    """
    call_edges = G.get_edges_by_type('CALLS')
    added_edge_list = []
    for call_edge in call_edges:
        caller_id = call_edge[0]
        callee_id = call_edge[1]

        # incase caller is not a CPG node, find the nearest
        # CPG node
        CPG_caller_id = G.find_nearest_upper_CPG_node(caller_id)
        entry_edge = G.get_out_edges(callee_id, data = True, edge_type = 'ENTRY')[0]
        # add CFG edge to ENTRY
        ln1 = G.get_node_attr(CPG_caller_id).get('lineno:int')
        ln2 = G.get_node_attr(list(G.get_in_edges(entry_edge[1]))[0][0]).get('lineno:int')
        ln2 = 'Line ' + ln2 if ln2 else 'Built-in'
        logger.info(sty.ef.inverse + sty.fg.cyan + 'Add CFG edge' + sty.rs.all + ' {} -> {} (Line {} -> {})'.format(CPG_caller_id, entry_edge[1], ln1, ln2))
        # assert CPG_caller_id != None, "Failed to add CFG edge. CPG_caller_id is None."
        # assert entry_edge[1] != None, "Failed to add CFG edge. Callee ENTRY is None."
        added_edge_list.append((CPG_caller_id, entry_edge[1], {'type:TYPE': 'FLOWS_TO'}))

        # add DF edge to PARAM
        # the order of para in paras matters!
        caller_para_names = get_argnames_from_funcaller(G, caller_id)
        callee_paras = get_argids_from_funcallee(G, callee_id)
        for idx in range(min(len(callee_paras), len(caller_para_names))):
            ln2 = G.get_node_attr(callee_paras[idx]).get('lineno:int')
            logger.info(sty.ef.inverse + sty.fg.li_magenta + 'Add INTER_FUNC_REACHES' + sty.rs.all + ' {} -> {} (Line {} -> Line {})'.format(CPG_caller_id, callee_paras[idx], ln1, ln2))
            assert CPG_caller_id != None, "Failed to add CFG edge. CPG_caller_id is None."
            assert callee_paras[idx] != None, f"Failed to add CFG edge. callee_paras[{idx}] is None."
            added_edge_list.append((CPG_caller_id, callee_paras[idx], {'type:TYPE': 'INTER_FUNC_REACHES', 'var': str(caller_para_names[idx])}))

        # add data flows for return values
        for child in G.get_child_nodes(callee_id, 'PARENT_OF'):
            if G.get_node_attr(child)['type'] == 'AST_STMT_LIST':
                for stmt in G.get_child_nodes(child, 'PARENT_OF'):
                    if G.get_node_attr(stmt)['type'] == 'AST_RETURN':
                        ln1 = G.get_node_attr(stmt).get('lineno:int')
                        ln2 = G.get_node_attr(CPG_caller_id).get('lineno:int')
                        logger.info(sty.ef.inverse + sty.fg.li_magenta + 'Add return value data flow' + sty.rs.all + ' {} -> {} (Line {} -> Line {})'.format(stmt, CPG_caller_id, ln1, ln2))
                        assert stmt != None, "Failed to add CFG edge. Statement ID is None."
                        assert CPG_caller_id != None, "Failed to add CFG edge. CPG_caller_id is None."
                        added_edge_list.append((stmt, CPG_caller_id, {'type:TYPE': 'FLOWS_TO'}))

    G.add_edges_from_list_if_not_exist(added_edge_list)

def register_func(G, node_id):
    """
    deprecated

    register the function to the nearest parent function like node
    we assume the 1-level parent node is the stmt of parent function

    Args:
        G: the graph object
        node_id: the node that needed to be registered
    """
    # we assume this node only have one parent node
    # sometimes this could be the root node and do not have any parent nodes
    if len(G.get_in_edges(node_id, edge_type="PARENT_OF")) == 0:
        return None
    parent_stmt_nodeid = G.get_in_edges(node_id, edge_type = "PARENT_OF")[0][0]
    parent_func_nodeid = G.get_in_edges(parent_stmt_nodeid, edge_type = "PARENT_OF")[0][0]
    G.set_node_attr(parent_func_nodeid, ("HAVE_FUNC", node_id))
    if parent_func_nodeid not in registered_func:
        registered_func[parent_func_nodeid] = set()
    registered_func[parent_func_nodeid].add(node_id)

    logger.info(sty.ef.b + sty.fg.green + "REGISTER {} to {}".format(node_id, parent_func_nodeid) + sty.rs.all)

def find_prop_legacy(G, parent_objs, prop_name, branches=None,
    side=None, parent_name='Unknown', in_proto=False, depth=0,
    prop_name_for_tags=None, ast_node=None, prop_name_sources=[]):
    '''
    Recursively find a property under parent_objs and its __proto__.
    
    Args:
        G (Graph): graph.
        parent_objs (list): parent objects.
        prop_name (str): property name.
        branches (BranchTagContainer, optional): branch information.
            Defaults to None.
        side (str, optional): 'left' or 'right', denoting left side or
            right side of assignment. Defaults to None.
        parent_name (str, optional): parent object's name, only used to
            print log. Defaults to ''.
        in_proto (bool, optional): whether __proto__ is being searched.
            Defaults to False.
        prop_name_for_tags (list, optional): Experimental. For-tags
            related to the property name. Defaults to None.
    
    Returns:
        prop_name_nodes, prop_obj_nodes: two sets containing possible
            name nodes and object nodes.
    '''
    if depth == 5:
        return [], []

    if in_proto:
        logger.debug('Cannot find "direct" property, going into __proto__ ' \
                f'{parent_objs}...')
        logger.debug(f'  {parent_name}.{prop_name}')
    prop_name_nodes = set()
    prop_obj_nodes = set()
    for parent_obj in parent_objs:
        if prop_name == wildcard and not is_wildcard_obj(G, parent_obj) and \
            not G.check_proto_pollution:
            continue

        # # filter out unrelated possibilities
        # skip = False
        # parent_matched_tags = BranchTagContainer(G.get_node_attr(parent_obj)
        #     .get('for_tags', [])).get_matched_tags(branches, level=1)
        # # print(f'{sty.fg.yellow}Parent obj {parent_obj},'
        # #     f' parent name {parent_name}, prop name {prop_name},'
        # #     f' current tags: {branches},'
        # #     f' parent tags: {G.get_node_attr(parent_obj).get("for_tags", [])},'
        # #     f' parent matched tags: {parent_matched_tags},'
        # #     f' prop name for tags: {prop_name_for_tags}'
        # #     + sty.rs.all)
        # if prop_name_for_tags:
        #     for t1 in parent_matched_tags:
        #         for t2 in prop_name_for_tags:
        #             if t1.point == t2.point and t1.branch != t2.branch:
        #                 skip = True
        #                 # print(f'{sty.fg.red}Skip parent obj {parent_obj} and '
        #                 #     f'prop name {prop_name} because of {t1}, {t2}'
        #                 #     + sty.rs.all)
        #                 break
        #         if skip:
        #             break
        # if skip:
        #     continue

        # flag of whether any name node with prop_name under this parent
        # object is found
        name_node_found = False
        # search "direct" properties
        prop_name_node = G.get_prop_name_node(prop_name, parent_obj)
        if prop_name_node is not None:
            name_node_found = True
            prop_name_nodes.add(prop_name_node)
            prop_objs = G.get_objs_by_name_node(prop_name_node,
                branches=branches)
            if prop_objs:
                prop_obj_nodes.update(prop_objs)
        elif prop_name != '__proto__' and prop_name != wildcard:
            # if name node is not found, search the property under __proto__
            # note that we cannot search "__proto__" under __proto__
            __proto__name_node = G.get_prop_name_node("__proto__", parent_obj)
            if __proto__name_node is not None:
                __proto__obj_nodes = G.get_objs_by_name_node(
                    __proto__name_node, branches)
                # if set(__proto__obj_nodes) & set(parent_objs):
                #     logger.error('__proto__ ' \
                #         f'{__proto__obj_nodes} and parent {parent_objs} ' \
                #         'object nodes have intersection')
                #     __proto__obj_nodes = list(set(__proto__obj_nodes) -
                #         set(parent_objs))
                if parent_obj in __proto__obj_nodes:
                    logger.error('__proto__ ' \
                        f'{__proto__obj_nodes} and parent {parent_obj} ' \
                        'have intersection')
                    __proto__obj_nodes = __proto__obj_nodes.remove(parent_obj)
                if __proto__obj_nodes:
                    __name_nodes, __obj_nodes = find_prop_legacy(G,
                        __proto__obj_nodes, prop_name, branches,
                        parent_name=parent_name + '.__proto__',
                        in_proto=True, depth=depth+1)
                    if __name_nodes:
                        name_node_found = True
                        prop_name_nodes.update(__name_nodes)
                        prop_obj_nodes.update(__obj_nodes)
        if not name_node_found and not in_proto and prop_name != wildcard and \
            side != 'left':
            # try wildcard (*)
            r1, r2 = find_prop_legacy(G, [parent_obj], wildcard, branches, side,
                parent_name, in_proto, depth, prop_name_for_tags)
            if r2:
                name_node_found = True
                prop_name_nodes.update(r1)
                prop_obj_nodes.update(r2)
                if is_wildcard_obj(G, parent_obj):
                    for o in r2:
                        for s in prop_name_sources:
                            add_contributes_to(G, [s], o)
        if not name_node_found and not in_proto:
            # we cannot create name node under __proto__
            # name nodes are only created under the original parent objects
            if is_wildcard_obj(G, parent_obj) and side != 'left':
                # if this is an wildcard (unknown) object, add another
                # wildcard object as its property
                added_name_node = G.add_prop_name_node(prop_name, parent_obj)
                prop_name_nodes.add(added_name_node)
                added_obj = G.add_obj_to_name_node(added_name_node,
                    js_type='object' if G.check_proto_pollution else None,
                    value=wildcard, ast_node=ast_node)                    
                prop_obj_nodes.add(added_obj)
                logger.debug('{} is a wildcard object, creating a wildcard'
                    ' object {} for its properties'.format(parent_obj,
                    added_obj))
                if G.get_node_attr(parent_obj).get('tainted'):
                    G.set_node_attr(added_obj, ('tainted', True))
                    logger.debug("{} marked as tainted [1]".format(added_obj))
                for s in prop_name_sources:
                    add_contributes_to(G, [s], added_obj)
                # if prop_name_for_tags:
                #     G.set_node_attr(added_name_node,
                #         ('for_tags', prop_name_for_tags))
            elif prop_name != wildcard: # normal (known) object
                if side == 'right':
                    continue
                elif parent_obj in [G.object_prototype, G.string_prototype,
                    G.function_prototype]: # more to be added
                    continue
                else:
                    # only add a name node
                    added_name_node = \
                        G.add_prop_name_node(prop_name, parent_obj)
                    prop_name_nodes.add(added_name_node)
                    # if prop_name_for_tags:
                    #     G.set_node_attr(added_name_node,
                    #                     ('for_tags', prop_name_for_tags))
                    logger.debug(f'{sty.ef.b}Add prop name node{sty.rs.all} '
                    f'{parent_name}.{prop_name} '
                    f'({parent_obj}->{added_name_node})')
    return prop_name_nodes, prop_obj_nodes

def find_prop(G: Graph, parent_objs, prop_name, branches=None,
    side=None, parent_name='Unknown', in_proto=False, depth=0,
    prop_name_for_tags=None, ast_node=None, prop_name_sources=[]):
    '''
    Recursively find a property under parent_objs and its __proto__.
    
    Args:
        G (Graph): graph.
        parent_objs (list): parent objects.
        prop_name (str): property name.
        branches (BranchTagContainer, optional): branch information.
            Defaults to None.
        side (str, optional): 'left' or 'right', denoting left side or
            right side of assignment. Defaults to None.
        parent_name (str, optional): parent object's name, only used to
            print log. Defaults to ''.
        in_proto (bool, optional): whether __proto__ is being searched.
            Defaults to False.
    
    Returns:
        prop_name_nodes: set of possible name nodes.
        prop_obj_nodes: set of possible object nodes.
        proto_is_tainted: if the property is found in __proto__, and
            __proto__ is tainted (modified by user input).
    '''
    if depth == 5:
        return [], [], None
    
    if in_proto:
        logger.debug('Cannot find "direct" property, going into __proto__ ' \
                f'{parent_objs}...')
        logger.debug(f'  {parent_name}.{prop_name}')

    prop_name_nodes = set()
    prop_obj_nodes = set()
    # multi_assign = False
    proto_is_tainted = False

    def add_arg_paths(obj_node, prop_name, prop_name_sources=[]):
        nonlocal G, parent_arg_paths
        # print('add arg paths', parent_arg_paths, obj_node, prop_name, prop_name_sources)
        arg_paths = G.get_node_attr(obj_node).get('arg_paths', set())
        # concrete property names
        if prop_name != wildcard:
            for arg_path in parent_arg_paths:
                new_arg_path = arg_path + '.' + str(prop_name)
                arg_paths.add(new_arg_path)
        if (len(prop_name_sources) == 1 # doesn't have to be wildcard
            # don't support multiple sources (from immediate values instead of obj nodes)
                and prop_name_sources[0] != obj_node): # no self reference
            prop_name_access_paths = G.get_node_attr(prop_name_sources[0]).get('arg_paths', set())
            for p in prop_name_access_paths:
                if '.' in p: # not a pure argument
                    continue # compound access paths are not supported yet
                for arg_path in parent_arg_paths:
                    new_arg_path = arg_path + '.' + p
                    arg_paths.add(new_arg_path)
        G.set_node_attr(obj_node, ('arg_paths', arg_paths))

    for parent_obj in parent_objs:
        # Argument access paths (for saved CF)
        parent_arg_paths = set(islice(
            G.get_node_attr(parent_obj).get('arg_paths', set()), 100))
        parent_arg_paths.add(parent_name)

        if prop_name == wildcard:
            if G.first_pass:
                obj = G.add_obj_node(ast_node, None, wildcard)
                add_arg_paths(obj, prop_name, prop_name_sources)
                prop_obj_nodes.add(obj)
                continue
            elif not is_wildcard_obj(G, parent_obj) and \
                    not G.check_proto_pollution and not G.check_ipt:
                continue

        if in_proto and G.get_node_attr(parent_obj).get('tainted'):
            proto_is_tainted = True
            logger.debug(f'__proto__ {parent_obj} is tainted.')

        # Flag of whether any concrete name node is found
        name_node_found = False
        # Flag of whether any wildcard name node is found
        wc_name_node_found = False

        # Search "direct" properties
        prop_name_node = G.get_prop_name_node(prop_name, parent_obj)
        if prop_name_node is not None and prop_name != wildcard:
            name_node_found = True
            prop_name_nodes.add(prop_name_node)
            prop_objs = G.get_objs_by_name_node(prop_name_node,
                branches=branches)
            if prop_objs:
                prop_obj_nodes.update(prop_objs)
            if G.first_pass:
                for obj in prop_objs:
                    if obj in G.inv_internal_objs:
                        pass
                    add_arg_paths(obj, prop_name, prop_name_sources)
                    # orig_arg_paths = \
                    #     G.get_node_attr(obj).get('arg_paths', set())
                    # new_arg_paths = set(arg_path + '.' + str(prop_name)
                    #                     for arg_path in parent_arg_paths)
                    # G.set_node_attr(obj,
                    #     ('arg_paths', orig_arg_paths.union(new_arg_paths)))
                    # print('!parent', parent_arg_paths, 'old', orig_arg_paths, 'new', new_arg_paths)

        # If name node is not found, search the property under __proto__.
        # Note that we cannot search "__proto__" under __proto__.
        elif (prop_name != '__proto__' and prop_name != wildcard
                and side != 'left'):
            __proto__name_node = G.get_prop_name_node("__proto__", parent_obj)
            if __proto__name_node is not None:
                __proto__obj_nodes = \
                    G.get_objs_by_name_node(__proto__name_node, branches)
                if parent_obj in __proto__obj_nodes:
                    logger.error(f'__proto__ {__proto__obj_nodes} and '
                        f'parent {parent_obj} have intersection')
                    __proto__obj_nodes = __proto__obj_nodes.remove(parent_obj)
                if G.first_pass:
                    for obj in __proto__obj_nodes:
                        if obj in G.inv_internal_objs or obj in G.builtin_prototypes:
                            pass
                        add_arg_paths(obj, '__proto__')
                        # orig_arg_paths = G.get_node_attr(obj).get('arg_paths', set())
                        # new_arg_paths = set(arg_path + '.__proto__'
                        #                     for arg_path in parent_arg_paths)
                        # G.set_node_attr(obj,
                        #     ('arg_paths', orig_arg_paths.union(new_arg_paths)))
                if __proto__obj_nodes:
                    __name_nodes, __obj_nodes, __t = find_prop(G,
                        __proto__obj_nodes, prop_name, branches,
                        parent_name=parent_name + '.__proto__',
                        in_proto=True, depth=depth+1,
                        ast_node=ast_node, prop_name_sources=prop_name_sources)
                    if __name_nodes:
                        name_node_found = True
                        prop_name_nodes.update(__name_nodes)
                        prop_obj_nodes.update(__obj_nodes)
                        if __t:
                            proto_is_tainted = True

        # If the property name is wildcard, fetch all properties
        if not in_proto and prop_name == wildcard:
            for name_node in G.get_prop_name_nodes(parent_obj):
                name = G.get_node_attr(name_node).get('name')
                if name == wildcard:
                    wc_name_node_found = True
                else:
                    name_node_found = True
                prop_name_nodes.add(name_node)
                prop_objs = G.get_objs_by_name_node(name_node,
                    branches=branches)
                if prop_objs:
                    prop_obj_nodes.update(prop_objs)
                if G.first_pass:
                    for obj in prop_objs:
                        if obj in G.inv_internal_objs or obj in G.builtin_prototypes:
                            pass
                        add_arg_paths(obj, prop_name, prop_name_sources)
                        # orig_arg_paths = \
                        #     G.get_node_attr(obj).get('arg_paths', set())
                        # new_arg_paths = set(arg_path + '.' + str(prop_name)
                        #                     for arg_path in parent_arg_paths)
                        # G.set_node_attr(obj,
                        #     ('arg_paths', orig_arg_paths.union(new_arg_paths)))
                        # print('!parent', parent_arg_paths, 'old', orig_arg_paths, 'new', new_arg_paths)

        # If the name node is not found, try wildcard (*).
        # If checking prototype pollution, add wildcard (*) results.
        if (not in_proto or G.check_ipt) and prop_name != wildcard and (
                not name_node_found or G.check_proto_pollution or G.check_ipt):
            prop_name_node = G.get_prop_name_node(wildcard, parent_obj)
            if prop_name_node is not None:
                wc_name_node_found = True
                prop_name_nodes.add(prop_name_node)
                prop_objs = G.get_objs_by_name_node(prop_name_node,
                    branches=branches)
                if prop_objs:
                    prop_obj_nodes.update(prop_objs)
                    if is_wildcard_obj(G, parent_obj):
                        for obj in prop_objs:
                            add_contributes_to(G, prop_name_sources, obj)
                            if G.first_pass and obj not in G.inv_internal_objs:
                                add_arg_paths(obj, prop_name, prop_name_sources)
                                # orig_arg_paths = \
                                #     G.get_node_attr(obj).get('arg_paths', set())
                                # new_arg_paths = set(arg_path + '.' + str(prop_name)
                                #                     for arg_path in parent_arg_paths)
                                # G.set_node_attr(obj,
                                #     ('arg_paths', orig_arg_paths.union(new_arg_paths)))
                                # print('!parent', parent_arg_paths, 'old', orig_arg_paths, 'new', new_arg_paths)

        # Create a name node if not found.
        # We cannot create name node under __proto__.
        # Name nodes are only created under the original parent objects.

        # If this is an wildcard (unknown) object, add another
        # wildcard object as its property.
        # Note that if it's on left side and the property name is
        # known, you need to create it with the concrete property name.
        if ((not in_proto or G.check_ipt) and is_wildcard_obj(G, parent_obj)
                and not wc_name_node_found
                and (side != 'left' or prop_name == wildcard)):
            added_name_node = G.add_prop_name_node(wildcard, parent_obj)
            prop_name_nodes.add(added_name_node)
            added_obj = G.add_obj_to_name_node(added_name_node,
                js_type='object' if G.check_proto_pollution or G.check_ipt
                else None, value=wildcard, ast_node=ast_node)                    
            prop_obj_nodes.add(added_obj)
            logger.debug('{} is a wildcard object, creating a wildcard'
                ' object {} for its properties'.format(parent_obj,
                added_obj))
            if G.first_pass and prop_name != wildcard:
                G.add_obj_as_prop(prop_name,
                    tobe_added_obj=added_obj, parent_obj=parent_obj)
            # propagate tags
            if G.get_node_attr(parent_obj).get('tainted'):
                G.set_node_attr(added_obj, ('tainted', True))
                # logger.debug("{} marked as tainted [1]".format(added_obj))
            if G.get_node_attr(parent_obj).get('fake_arg'):
                G.set_node_attr(added_obj, ('fake_arg', True))
            if G.get_node_attr(parent_obj).get('unresolved'):
                G.set_node_attr(added_obj, ('unresolved', True))
                G.set_node_attr(added_obj, ('how_to_resolve', G.get_node_attr(parent_obj).get('how_to_resolve')))
            for s in prop_name_sources:
                add_contributes_to(G, [s], added_obj)
            # if name_node_found:
            #     multi_assign = True
            wc_name_node_found = True
            if G.first_pass:
                arg_paths = set(arg_path + '.' + str(prop_name)
                                for arg_path in parent_arg_paths)
                G.set_node_attr(added_obj, ('arg_paths', arg_paths))
                # print('!parent', parent_arg_paths, 'new', arg_paths)
        # Normal (known) object and concrete (known) property name,
        # or wildcard property name under normal (known) object
        elif not in_proto and ((not name_node_found and prop_name != wildcard)
                or (not wc_name_node_found and prop_name == wildcard)):
            if side == 'right':
                # Don't create anything on right side.
                # If the lookup failed, return empty results.
                continue
            elif parent_obj in G.builtin_prototypes:
                # Modifying internal prototypes are restricted
                # to avoid object explosion?
                logger.debug(
                    f'Trying to add prop name node under {parent_obj}')
                continue
            else:
                # On left side or normal property lookup,
                # only add a name node.
                # If there are multi-level property lookups, the object
                # node will be created on the lower level.
                added_name_node = \
                    G.add_prop_name_node(prop_name, parent_obj)
                prop_name_nodes.add(added_name_node)
                logger.debug(f'{sty.ef.b}Add prop name node{sty.rs.all} '
                    f'{parent_name}.{prop_name} '
                    f'({parent_obj}->{added_name_node})')
                if prop_name == wildcard:
                    wc_name_node_found = True
                    # if name_node_found:
                    #     multi_assign = True
                else:
                    name_node_found = True
    # multi_assign = name_node_found and wc_name_node_found
    return prop_name_nodes, prop_obj_nodes, proto_is_tainted

def handle_prop(G, ast_node, side=None, extra=ExtraInfo()) \
    -> Tuple[NodeHandleResult, NodeHandleResult]:
    '''
    Handle property.
    
    Args:
        G (Graph): graph.
        ast_node ([type]): the MemberExpression (AST_PROP) AST node.
        extra (ExtraInfo, optional): Extra information. Defaults to {}.
    
    Returns:
        handled property, handled parent
    '''
    # recursively handle both parts
    parent, prop = G.get_ordered_ast_child_nodes(ast_node)[:2]
    handled_parent = handle_node(G, parent, extra)
    handled_prop = handle_node(G, prop, extra)
    if G.finished or G.time_limit_reached:
        return NodeHandleResult(), handled_parent

    if handled_parent.tampered_prop:
        G.ipt_use.add(ast_node)
        logger.warning(sty.fg.li_red + sty.ef.inverse + 'Possible internal'
            ' property tampering (parent is tampered) at node {} (Line {})'
            .format(ast_node, G.get_node_attr(ast_node).get('lineno:int'))
            + sty.rs.all)
    
    parent_code = G.get_node_attr(parent).get('code')
    parent_name = handled_parent.name or parent_code or 'Unknown'
    parent_objs = handled_parent.obj_nodes
    parent_name_nodes = handled_parent.name_nodes

    branches = extra.branches
    # side = extra.side # NOTE: Do not use extra.side, may have been removed
    prop_name_nodes, prop_obj_nodes = set(), set()

    # prepare property names
    prop_names, prop_name_sources, prop_name_tags = \
                            to_values(G, handled_prop, for_prop=True)
    name_tainted = False
    if G.check_proto_pollution or G.check_ipt:
        for source in chain(*prop_name_sources):
            if G.get_node_attr(source).get('tainted'):
                name_tainted = True
                break

    parent_is_proto = False
    if G.check_proto_pollution:
        for obj in handled_parent.obj_nodes:
            if obj in G.builtin_prototypes:
                parent_is_proto = True
                break

    # NOTE: wildcard lookup has been moved to find_prop
    # if G.check_proto_pollution and prop_names == [wildcard] * len(prop_names):
        # conservative: only if all property names are unknown,
        # we fetch all properties
        # (including __proto__ for prototype pollution detection)
        # logger.debug('All property names are unknown, fetching all properties')
    # if G.check_proto_pollution and wildcard in prop_names:
    #     # agressive: if any property name is unknown, we fetch all properties
    #     logger.debug('One of property names is unknown, fetching all properties')
    #     for parent_obj in parent_objs:
    #         prop_name_nodes.update(G.get_prop_name_nodes(parent_obj))
    #         objs = G.get_prop_obj_nodes(parent_obj, branches=branches,
    #             exclude_proto=False)
    #         objs = filter(lambda obj: obj in G.builtin_constructors or
    #                       G.get_node_attr(obj).get('type') != 'function', objs)
    #         prop_obj_nodes.update(objs)
    #         if is_wildcard_obj(G, parent_obj) and not G.get_prop_obj_nodes(
    #                 parent_obj, wildcard, extra.branches):
    #             added_obj = \
    #                 G.add_obj_as_prop(wildcard, ast_node,
    #                         parent_obj=parent_obj, value=wildcard)
    #             add_contributes_to(G, [parent_obj], added_obj)
    #             prop_obj_nodes.add(added_obj)
    #     name = f'{parent_name}.*'

    # else:

    # create parent object if it doesn't exist
    parent_objs = list(filter(lambda x: x != G.undefined_obj, parent_objs))
    if not parent_objs:
        logger.debug(
            "PARENT OBJ {} NOT DEFINED, creating object nodes".
            format(parent_name))
        # we assume this happens when it's a built-in var name
        if parent_name_nodes:
            parent_objs = []
            for name_node in parent_name_nodes:
                obj = G.add_obj_to_name_node(name_node, ast_node,
                    js_type='object' if G.check_proto_pollution or G.check_ipt
                    else None, value=wildcard)
                parent_objs.append(obj)
        else:
            obj = G.add_obj_to_scope(parent_name, ast_node,
                js_type='object' if G.check_proto_pollution or G.check_ipt
                else None, scope=G.BASE_SCOPE, value=wildcard)
            parent_objs = [obj]
        # else:
        #     logger.debug("PARENT OBJ {} NOT DEFINED, return undefined".
        #         format(parent_name))
        #     return NodeHandleResult()

    multi_assign = False
    tampered_prop = False
    # find property name nodes and object nodes
    # (filtering is moved to find_prop)
    for i, prop_name in enumerate(prop_names):
        assert prop_name is not None
        name_nodes, obj_nodes, proto_is_tainted = \
            find_prop(G, parent_objs, prop_name,
            branches, side, parent_name,
            prop_name_for_tags=prop_name_tags[i],
            ast_node=ast_node, prop_name_sources=prop_name_sources[i])
        prop_name_nodes.update(name_nodes)
        prop_obj_nodes.update(obj_nodes)
        if prop_name == wildcard:
        # if _multi_assign:
            # NOTE: This is not fine grained. If a property name causes
            #       multi_assign, all properties will be assigned with
            #       multiple possibilities.
            multi_assign = True
        if G.check_ipt and side != 'left' and proto_is_tainted:
            # G.ipt_use.add(ast_node) # we don't detect it for now
            tampered_prop = True
            logger.warning(sty.fg.li_red + sty.ef.inverse + 'Possible internal'
                ' property tampering (any use) at node {} (Line {})'
                .format(ast_node, G.get_node_attr(ast_node).get('lineno:int'))
                + sty.rs.all)

    # wildcard is now implemented in find_prop

    if len(prop_names) == 1:
        name = f'{parent_name}.{prop_names[0]}'
    else:
        name = f'{parent_name}.{"/".join(map(str, prop_names))}'

    # tricky fix, we don't really link name nodes to the undefined object
    if not prop_obj_nodes:
        prop_obj_nodes = set([G.undefined_obj])

    return NodeHandleResult(obj_nodes=list(prop_obj_nodes),
            name=f'{name}', name_nodes=list(prop_name_nodes),
            ast_node=ast_node, callback=get_df_callback(G),
            name_tainted=name_tainted, parent_is_proto=parent_is_proto,
            multi_assign=multi_assign, tampered_prop=tampered_prop
        ), handled_parent

def handle_assign(G, ast_node, extra=None, right_override=None):
    '''
    Handle assignment statement.
    '''
    if extra is None:
        extra = ExtraInfo()
    # get AST children (left and right sides)
    ast_children = G.get_ordered_ast_child_nodes(ast_node)
    try:
        left, right = ast_children
    except ValueError:
        # if only have left side
        return handle_node(G, ast_children[0], extra)

    # get branch tags
    branches = extra.branches if extra else BranchTagContainer()

    # recursively handle both sides
    # handle right first
    if right_override is None:
        handled_right = \
            handle_node(G, right, ExtraInfo(extra, side='right'))
    else:
        handled_right = right_override
    # handle left
    if G.get_node_attr(left).get('type') == 'AST_ARRAY':
        # destructuring assignment
        # handle left item by item
        children = G.get_ordered_ast_child_nodes(left)
        if G.get_node_attr(left).get('flags:string[]') == 'JS_OBJECT':
            # ObjectPattern assignments
            added_obj = G.add_obj_node(ast_node=ast_node, js_type='object')
            for child in children:
                value, key = G.get_ordered_ast_child_nodes(child)
                handled_left = \
                    handle_var(G, value, side='left', extra=extra)
                _key = G.get_name_from_child(key)
                for obj in handled_right.obj_nodes:
                    prop_obj_nodes= G.get_prop_obj_nodes(parent_obj=obj,
                        prop_name=_key, branches=branches)
                    for o in prop_obj_nodes:
                        G.add_obj_as_prop(parent_obj=added_obj,
                            prop_name=_key, tobe_added_obj=o)
                    do_assign(G, handled_left, NodeHandleResult(
                        obj_nodes=prop_obj_nodes), branches, ast_node)
            return NodeHandleResult(obj_nodes=[added_obj])
        else:
            # ArrayPattern assignments
            added_obj = G.add_obj_node(ast_node=ast_node, js_type='array')
            for i, child in enumerate(children):
                handled_left = \
                    handle_var(G, child, side='left', extra=extra)
                for obj in handled_right.obj_nodes:
                    prop_obj_nodes= G.get_prop_obj_nodes(parent_obj=obj,
                        prop_name=str(i), branches=branches)
                    for o in prop_obj_nodes:
                        G.add_obj_as_prop(parent_obj=added_obj,
                            prop_name=str(i), tobe_added_obj=o)
                    do_assign(G, handled_left, NodeHandleResult(
                        obj_nodes=prop_obj_nodes), branches, ast_node)
            G.add_obj_as_prop(parent_obj=added_obj, prop_name='length',
                js_type='number', value=len(children), ast_node=ast_node)
            return NodeHandleResult(obj_nodes=[added_obj])
    else:
        # normal assignment
        handled_left = handle_node(G, left, ExtraInfo(extra, side='left'))
        # set function name (alias by assignment)
        name = handled_left.name
        if name and G.get_node_attr(right).get('type') in \
            ['AST_FUNC_DECL', 'AST_CLOSURE', 'AST_METHOD']:
            for func_obj in handled_right.obj_nodes:
                old_name = G.get_node_attr(func_obj).get('name')
                if not old_name or old_name.startswith('{anon'):
                    G.set_node_attr(func_obj, ('name', name))
                    G.set_node_attr(right, ('alias', name))
                # func_ast = G.get_obj_def_ast_node(func_obj, aim_type='function')
                # if func_ast:
                #     aliases = G.get_node_attr(func_obj).get('aliases', set())
                #     aliases.add(name)
                #     G.set_node_attr(func_obj, ('aliases', aliases))
        return do_assign(G, handled_left, handled_right, branches, ast_node)

def do_assign(G, handled_left, handled_right, branches=None, ast_node=None):
    if branches is None:
        branches = BranchTagContainer()

    if not handled_left:
        logger.warning("Left side handling error at statement {}".format(ast_node))
        return NodeHandleResult()

    if not handled_right:
        logger.warning("Right side handling error at statement {}".format(ast_node))
        return NodeHandleResult()

    right_objs = to_obj_nodes(G, handled_right, ast_node)

    if not right_objs:
        logger.debug("Right OBJ not found")
        right_objs = [G.undefined_obj]

    # returned objects for serial assignment (e.g. a = b = c)
    returned_objs = []

    # print('parent is proto =', handled_left.parent_is_proto, 'name tainted =', handled_left.name_tainted)

    if G.check_proto_pollution and ast_node is not None and \
            handled_left.name_tainted and handled_left.parent_is_proto:
        flag1 = False
        flag2 = False
        # for name_node in handled_left.name_nodes:
        #     if name_node in G.pollutable_name_nodes:
        #         flag1 = True
        #         break
        # for obj_node in handled_left.obj_nodes:
        #     if obj_node in G.pollutable_objs:
        #         flag1 = True
        #         break
        for obj in right_objs:
            if G.get_node_attr(obj).get('tainted'):
                flag2 = True
                break
        # print('right object is tainted =', flag2)
        if flag2:
            name_node_log = [('{}: {}'.format(x, repr(G.get_node_attr(x)
                .get('name')))) for x in handled_left.name_nodes]
            logger.warning(sty.fg.li_red + sty.ef.inverse +
                'Possible prototype pollution at node {} (Line {}), '
                'trying to assign {} to name node {}'
                .format(ast_node, G.get_node_attr(ast_node).get('lineno:int'),
                right_objs, ', '.join(name_node_log)) + sty.rs.all)
            logger.debug(f'Pollutable objs: {G.pollutable_objs}')
            logger.debug(f'Pollutable NN: {G.pollutable_name_nodes}')
            # commented because of the new prototype pollution detection
            # G.proto_pollution.add(ast_node)
            if G.exit_when_found:
                G.finished = True
            # skip doing the assignment
            return NodeHandleResult()

    if G.check_ipt and ast_node is not None and handled_left.name_tainted and \
            any(map(lambda nn: G.get_node_attr(nn).get('name') == '__proto__',
            handled_left.name_nodes)):
        G.ipt_write.add(ast_node)

    if not handled_right.obj_nodes and handled_right.terminated:
        # skip doing the assignment
        return NodeHandleResult()

    # do the assignment
    for name_node in handled_left.name_nodes:
        # nn_for_tags = G.get_node_attr(name_node).get('for_tags')
        # if not nn_for_tags: # empty array or None
        G.assign_obj_nodes_to_name_node(name_node, right_objs,
            branches=branches, multi=handled_left.multi_assign)
        returned_objs.extend(right_objs)
        # else:
        #     logger.debug(f"  name node's for tags {nn_for_tags}")
        #     for obj in right_objs:
        #         obj_for_tags = G.get_node_attr(obj).get('for_tags', [])
        #         flag = 2 # 0: ignore, 1: assign, 2: copy
        #         for tag1 in nn_for_tags:
        #             for tag2 in obj_for_tags:
        #                 if tag1 == tag2: # if tags are completely matched
        #                     flag = 1
        #                     break
        #                 elif (tag1.point == tag2.point
        #                     and tag1.branch == tag2.branch):
        #                     # if tags are partially matched,
        #                     # the object will be ignored
        #                     flag = 0
        #                     break
        #             # if no matched tags, the object will be copied
        #             if flag != 2:
        #                 break
        #         if flag == 1: # assign
        #             G.assign_obj_nodes_to_name_node(name_node, [obj],
        #                 branches=branches)
        #             returned_objs.append(obj)
        #             logger.debug(f'  found matching obj {obj} with tags {obj_for_tags}')
        #         elif flag == 2: # copy
        #             copied_obj = G.copy_obj(obj)
        #             for_tags = G.get_node_attr(obj).get('for_tags',
        #                                                 BranchTagContainer())
        #             new_for_tags = [BranchTag(i, mark='C')
        #                 for i in BranchTagContainer(nn_for_tags)
        #                 .get_matched_tags(branches, level=1)]
        #             for_tags.extend(new_for_tags)
        #             G.set_node_attr(copied_obj, ('for_tags', for_tags))
        #             G.assign_obj_nodes_to_name_node(name_node, [copied_obj],
        #                 branches=branches)
        #             returned_objs.append(copied_obj)
        #             logger.debug(f'  copied from obj {obj} with tags {for_tags}')

    # used_objs = handled_right.used_objs
    # logger.debug(f'  assign used objs={used_objs}')

    return NodeHandleResult(obj_nodes=handled_right.obj_nodes,
        name_nodes=handled_left.name_nodes, # used_objs=used_objs,
        callback=get_df_callback(G))

def handle_op_simple(G, ast_node, extra=ExtraInfo()):
    left_child, right_child = G.get_ordered_ast_child_nodes(ast_node)
    handled_left = handle_node(G, left_child, extra)
    handled_right = handle_node(G, right_child, extra)
    values1, sources1, tags1 = to_values(G, handled_left, ast_node)
    values2, sources2, tags2 = to_values(G, handled_right, ast_node)
    used_objs = []
    used_objs.extend(handled_left.obj_nodes)
    used_objs.extend(handled_right.obj_nodes)
    used_objs = list(set(used_objs))
    results = [wildcard]
    result_sources = [list(chain(used_objs, *sources1, *sources2))]
    res = NodeHandleResult(ast_node=ast_node, values=results,
        used_objs=used_objs, value_sources=result_sources,
        callback=get_df_callback(G))
    if G.get_node_attr(ast_node).get('type') == 'AST_ASSIGN_OP':
        do_assign(G, handled_left, NodeHandleResult(values=results),
                  branches=extra.branches, ast_node=ast_node)
    return res

def handle_op_by_values(G, ast_node, extra=ExtraInfo(), combine=True, saved={}):
    left_child, right_child = G.get_ordered_ast_child_nodes(ast_node)
    flag = G.get_node_attr(ast_node).get('flags:string[]')
    handled_left = handle_node(G, left_child, extra)
    handled_right = handle_node(G, right_child, extra)
    values1, sources1, tags1 = to_values(G, handled_left, ast_node)
    values2, sources2, tags2 = to_values(G, handled_right, ast_node)
    used_objs = []
    used_objs.extend(handled_left.obj_nodes)
    used_objs.extend(handled_right.obj_nodes)
    used_objs = list(set(used_objs))
    func_scope = G.find_ancestor_scope()
    if len(values1) * len(values2) > G.op_value_limit:
        if (func_scope, ast_node) in saved:
            return saved[(func_scope, ast_node)]
    # calculate values
    results = []
    result_sources = []
    result_tags = []
    if flag == 'BINARY_ADD':
        for i, v1 in enumerate(values1):
            for j, v2 in enumerate(values2):
                if v1 != wildcard and v2 != wildcard:
                    if (type(v1) == int or type(v1) == float) and \
                        (type(v2) == int or type(v2) == float):
                        results.append(v1 + v2)
                    else:
                        results.append(str(v1) + str(v2))
                else:
                    results.append(wildcard)
                result_tags.append(tags1 + tags2)
                result_sources.append((sources1[i] or []) + (sources2[j] or []))
        if len(values1) * len(values2) == 0:
            # always returns at least one value
            results.append(wildcard)
            sources = set()
            for s in sources1 + sources2:
                sources.update(s)
            result_sources.append(list(sources))
    elif flag == 'BINARY_SUB':
        for i, v1 in enumerate(values1):
            for j, v2 in enumerate(values2):
                if v1 != wildcard and v2 != wildcard:
                    try:
                        results.append(float(v1) - float(v2))
                    except ValueError:
                        results.append(float('nan'))
                else:
                    results.append(wildcard)
                result_tags.append(tags1 + tags2)
                result_sources.append((sources1[i] or []) + (sources2[j] or []))
        if len(values1) * len(values2) == 0:
            results.append(wildcard)
            sources = set()
            for s in sources1 + sources2:
                sources.update(s)
            result_sources.append(list(sources))
    if combine:
        results, result_sources = combine_values(results, result_sources)
    res = NodeHandleResult(ast_node=ast_node, values=results,
        used_objs=used_objs, value_sources=result_sources,
        callback=get_df_callback(G))
    if G.get_node_attr(ast_node).get('type') == 'AST_ASSIGN_OP':
        do_assign(G, handled_left, NodeHandleResult(values=results),
                  branches=extra.branches, ast_node=ast_node)
    if len(results) > G.op_value_limit:
        saved[(func_scope, ast_node)] = res
    return res

def handle_op_by_objs(G, ast_node, extra=ExtraInfo(), saved={}):
    left_child, right_child = G.get_ordered_ast_child_nodes(ast_node)
    flag = G.get_node_attr(ast_node).get('flags:string[]')
    handled_left = handle_node(G, left_child, extra)
    handled_right = handle_node(G, right_child, extra)
    left_objs = to_obj_nodes(G, handled_left, ast_node)
    right_objs = to_obj_nodes(G, handled_right, ast_node)
    func_scope = G.find_ancestor_scope()
    used_objs = set()
    if len(left_objs) * len(right_objs) > G.op_obj_node_limit:
        if (func_scope, ast_node) in saved:
            return saved[(func_scope, ast_node)]
    def get_value_and_type(node):
        nonlocal G
        attrs = G.get_node_attr(node)
        value = attrs.get('code')
        if value is None:
            value = wildcard
        return value, attrs.get('type')
    results = []
    if flag == 'BINARY_ADD':
        for i, o1 in enumerate(left_objs):
            for j, o2 in enumerate(right_objs):
                v1, t1 = get_value_and_type(o1)
                v2, t2 = get_value_and_type(o2)
                if v1 != wildcard and v2 != wildcard:
                    if t1 == 'number' and t2 == 'number':
                        result = float(v1 + v2)
                        t = 'number'
                        op = 'numeric_add'
                    else:
                        result = str(v1) + str(v2)
                        t = 'string'
                        op = 'string_concat'
                else:
                    result = wildcard
                    t = None # implies 'object'
                    op = 'unknown_add'
                result_obj = G.add_obj_node(ast_node, t, result)
                # logger.log(ATTENTION, f'{v1} + {v2}: {o1} {o2} -> {result_obj}')
                add_contributes_to(G, [o1, o2], result_obj, op)
                results.append(result_obj)
                used_objs.add(o1)
                used_objs.add(o2)
        if len(left_objs) * len(right_objs) == 0:
            # always returns at least one value
            results.append(G.add_obj_node(ast_node, None, wildcard))
    elif flag == 'BINARY_SUB':
        for i, o1 in enumerate(left_objs):
            for j, o2 in enumerate(right_objs):
                v1, _ = get_value_and_type(o1)
                v2, _ = get_value_and_type(o2)
                if v1 != wildcard and v2 != wildcard:
                    try:
                        result = float(v1) - float(v2)
                        t = 'number'
                    except ValueError:
                        result = float('nan')
                        t = 'number'
                else:
                    result = wildcard
                    t = None # implies 'object'
                result_obj = G.add_obj_node(ast_node, t, result)
                add_contributes_to(G, [o1, o2], result_obj, 'sub')
                results.append(result_obj)
                used_objs.add(o1)
                used_objs.add(o2)
        if len(left_objs) * len(right_objs) == 0:
            # always returns at least one value
            results.append(G.add_obj_node(ast_node, None, wildcard))
    if G.get_node_attr(ast_node).get('type') == 'AST_ASSIGN_OP':
        do_assign(G, handled_left, NodeHandleResult(obj_nodes=results),
            branches=extra.branches, ast_node=ast_node)
    res = NodeHandleResult(ast_node=ast_node, obj_nodes=results,
        used_objs=list(used_objs), callback=get_df_callback(G))
    if len(results) > G.op_obj_node_limit:
        saved[(func_scope, ast_node)] = res
    return res


def handle_template(G: Graph, ast_node, extra=ExtraInfo()):
    '''
    Handle template strings by DFS. Be aware of possible possibility
    explosion. The number of possibilites is the product of the number
    of each element.

    Args:
        G (Graph): Graph.
        ast_node: AST node of the template string.
        extra (ExtraInfo, optional): Extra info

    Returns:
        list, set: List of result objects, set of used objects.
    '''
    children = G.get_ordered_ast_child_nodes(ast_node)
    if len(children) == 0:
        return NodeHandleResult(ast_node=ast_node, 
                                values=[""], value_sources=[[ast_node]])
    if len(children) == 1:
        return handle_node(G, children[0], extra)
    results = []
    all_used_objs = set()
    def dfs(i=0, buffer="", used_objs=[]):
        nonlocal G, children, results, ast_node, extra
        if i == len(children):
            result_obj = G.add_obj_node(ast_node, 'string', value=buffer)
            add_contributes_to(G, used_objs, result_obj,
                               operation='string_concat')
            results.append(result_obj)
            all_used_objs.update(used_objs)
            return
        handled_element = handle_node(G, children[i], extra)
        objs = to_obj_nodes(G, handled_element, ast_node=children[i])
        for obj in objs:
            typ = G.get_node_attr(obj).get('type')
            value = val_to_str(G.get_node_attr(obj).get('code'))
            if buffer == wildcard or value == wildcard:
                dfs(i + 1, wildcard, used_objs + [obj])
            elif typ == 'string':
                dfs(i + 1, buffer + value, used_objs + [obj])
            else: # including 'number'
                dfs(i + 1, buffer + val_to_str(value), used_objs + [obj])
    dfs()
    return NodeHandleResult(ast_node=ast_node, obj_nodes=results,
        used_objs=list(all_used_objs), callback=get_df_callback(G))


def has_else(G, if_ast_node):
    '''
    Check if an if statement has 'else'.
    '''
    # Check by finding if the last if element's condition is NULL
    elems = G.get_ordered_ast_child_nodes(if_ast_node)
    if elems:
        last_elem = elems[-1]
        cond = G.get_ordered_ast_child_nodes(last_elem)[0]
        if G.get_node_attr(cond).get('type') == 'NULL':
            return True
    return False

def instantiate_obj(G, exp_ast_node, constructor_decl, branches=None):
    '''
    Instantiate an object (create a new object).
    
    Args:
        G (Graph): Graph.
        exp_ast_node: The New expression's AST node.
        constructor_decl: The constructor's function declaration AST
            node.
        branches (optional): Branch information.. Defaults to [].
    
    Returns:
        obj_node: The created object. Note that this function returns a
            single object (not an array of objects).
        returned_obj: list, The return object of the function
    '''
    # create the instantiated object
    # js_type=None: avoid automatically adding prototype
    created_obj = G.add_obj_node(ast_node=exp_ast_node, js_type=None)
    # add edge between obj and obj decl
    G.add_edge(created_obj, constructor_decl, {"type:TYPE": "OBJ_DECL"})
    # build the prototype chain
    G.build_proto(created_obj)

    # update current object (this)
    backup_objs = G.cur_objs
    G.cur_objs = [created_obj]

    returned_objs, _ = simurun_function(G, constructor_decl, branches=branches,
        caller_ast=exp_ast_node)

    G.cur_objs = backup_objs

    # finally add call edge from caller to callee
    # added in call_function, no need to add here
    # if exp_ast_node is not None:
    #     G.add_edge_if_not_exist(exp_ast_node, constructor_decl,
    #                             {"type:TYPE": "CALLS"})

    return created_obj, returned_objs

def handle_var(G: Graph, ast_node, side=None, extra=None):
    cur_node_attr = G.get_node_attr(ast_node)
    var_name = G.get_name_from_child(ast_node)

    if var_name == 'this' and G.cur_objs:
        now_objs = G.cur_objs
        name_node = None
    elif var_name == '__filename':
        return NodeHandleResult(name=var_name, values=[
            G.get_cur_file_path()], ast_node=ast_node)
    elif var_name == '__dirname':
        return NodeHandleResult(name=var_name, values=[os.path.join(
            G.get_cur_file_path(), '..')], ast_node=ast_node)
    else:
        now_objs = []
        branches = extra.branches if extra else BranchTagContainer()

        name_node = G.get_name_node(var_name)
        if name_node is not None:
            now_objs = list(
                set(G.get_objs_by_name_node(name_node, branches=branches)))
        elif side != 'right':
            logger.log(ATTENTION, f'Name node {var_name} not found, create name node')
            if cur_node_attr.get('flags:string[]') == 'JS_DECL_VAR':
                # we use the function scope
                name_node = G.add_name_node(var_name,
                                scope=G.find_ancestor_scope())
            elif cur_node_attr.get('flags:string[]') in [
                'JS_DECL_LET', 'JS_DECL_CONST']:
                # we use the block scope                
                name_node = G.add_name_node(var_name, scope=G.cur_scope)
            else:
                # only if the variable is not defined and doesn't have
                # 'var', 'let' or 'const', we define it in the global scope
                name_node = G.add_name_node(var_name, scope=G.BASE_SCOPE)
        # else:
        #     now_objs = [G.undefined_obj]

    name_nodes = [name_node] if name_node is not None else []

    assert None not in now_objs

    # add from_branches information
    # from_branches = []
    # cur_branches = extra.branches if extra else BranchTagContainer()
    # for obj in now_objs:
    #     from_branches.append(cur_branches.get_matched_tags(
    #         G.get_node_attr(obj).get('for_tags') or []))

    # tricky fix, we don't really link name nodes to the undefined object
    if not now_objs:
        now_objs = [G.undefined_obj]

    return NodeHandleResult(obj_nodes=now_objs, name=var_name,
        name_nodes=name_nodes, # from_branches=[from_branches],
        ast_node=ast_node)

def handle_node(G: Graph, node_id, extra=None) -> NodeHandleResult:
    """
    for different node type, do different actions to handle this node
    """
    if G.function_time_limit and G.func_start_time is not None \
            and time.time() - G.func_start_time > G.function_time_limit:
        logger.warning('Function time limit reached. Halting...')
        G.time_limit_reached = True
    if G.finished or G.time_limit_reached:
        return NodeHandleResult()

    # Status output
    if G.output_status and time.time() - G.last_time > 10:
        input_hash = hashlib.md5(G.entry_file_path.encode('utf-8')).hexdigest()[:6]
        with open(f'status-{input_hash}.txt', 'w') as fp:
            covered_stmt = len(G.covered_stat)
            total_stmt = G.get_total_num_statements()
            fp.writelines([
                f'entry file: {G.entry_file_path}\n',
                f'current file: {G.file_stack[-1] if G.file_stack else None}\n',
                f'coarse (1st pass): {G.first_pass}\n',
                f'cg_paths: {G.cg_paths}\n',
                f'cf_paths: {G.cf_paths}\n',
                f'call_stack: {G.call_stack}\n',
                f'code coverage: {covered_stmt / total_stmt * 100:.2f}%\n'
                f'finished: {G.finished}\n',
                f'stack1: {len(G.stack1)} {G.stack1}\n',
                f'stack2: {len(G.stack2)} {G.stack2}\n',
                f'task_queue: {len(G.task_queue)} {G.task_queue}\n',
                f'microtask_queue: {len(G.microtask_queue)} {G.microtask_queue}\n',
            ])
            if G.last_handled is not None:
                fp.writelines([
                    f'last handled: {G.last_handled} {G.get_node_attr(G.last_handled)}\n',
                    f'last handled line: {G.last_handled_lineno}\n',
                ])
        G.last_time = time.time()

    cur_node_attr = G.get_node_attr(node_id)
    cur_type = cur_node_attr['type']
    cur_lineno = cur_node_attr.get('lineno:int')
    node_name = cur_node_attr.get('name') or \
                    G.get_name_from_child(node_id, max_depth=2, order=1)
    node_color = sty.fg.white + sty.bg.da_grey

    #print(cur_lineno, G.get_node_file_path(node_id))
    
    # for code coverage
    if G.is_statement(node_id):
        G.covered_stat.add(node_id)

    if G.get_node_attr(node_id).get('labels:label') == 'Artificial':
        node_color = sty.fg.white + sty.bg.red
    elif G.get_node_attr(node_id).get('labels:label') == 'Artificial_AST':
        node_color = sty.fg.black + sty.bg(179)
    node_code = G.get_node_attr(node_id).get('code')

    try:
        if len(node_code) > 100: node_code = ''
    except:
        node_code = ''

    logger.info(f"{sty.ef.b}{sty.fg.cyan}HANDLE NODE {node_id}{sty.rs.all}" +
        (f" (Line {cur_lineno})" if cur_lineno else "") +
        f": {node_color}{cur_type}{sty.rs.all}"
        f" {node_name or ''}{sty.rs.all}, {node_code or ''}")

    # remove side information
    # because assignment's side affects its direct children
    side = extra.side if extra else None
    extra = ExtraInfo(extra, side=None)

    loop_complexity_score = 1
    for i in G.for_stack:
        loop_complexity_score *= len(i[-1]) * len(i[-2])

    if cur_type == 'File' or cur_type == 'Directory':
        for child in list(G.get_child_nodes(node_id)):
            handle_node(G, child, extra)

    elif cur_type == "AST_ASSIGN":
        return handle_assign(G, node_id, extra)
    
    elif cur_type == "AST_TRY":
        children = G.get_ordered_ast_child_nodes(node_id)
        simurun_block(G, children[0], branches=extra.branches)
        for child in children[1:]:
            handle_node(G, child, extra)

    elif cur_type == "AST_YIELD": # await (instead of yield)
        promises = handle_node(G, G.get_ordered_ast_child_nodes(node_id)[0])
        returned_objs = set()
        # prepare a callback (onFulfilled) function
        def python_callback(
                G, caller_ast, extra, _, value=NodeHandleResult(), *args):
            nonlocal returned_objs
            returned_objs.update(to_obj_nodes(G, value, node_id))
            return NodeHandleResult()
        cb = G.add_blank_func_with_og_nodes(
            'pythonCallback', python_func=python_callback)
        # call promise.then
        for promise in promises.obj_nodes:
            then = G.get_prop_obj_nodes(
                        G.promise_prototype, 'then', extra.branches)
            result, _ = call_function(G, then,
                    args=[NodeHandleResult(obj_nodes=[cb])],
                    this=NodeHandleResult(obj_nodes=[promise]),
                    extra=extra, call_ast=node_id)
        # add control flows from the callback function's EXIT node to
        # the current statement
        cb_ast = G.get_obj_def_ast_node(cb)
        exit_node = G.get_successors(cb_ast, edge_type='EXIT')[0]
        G.add_edge_if_not_exist(exit_node,
            G.find_nearest_upper_CPG_node(node_id), {"type:TYPE": "FLOWS_TO"})
        return NodeHandleResult(ast_node=node_id,
                                obj_nodes=list(returned_objs),
                                used_objs=promises.obj_nodes,
                                callback=get_df_callback(G))

    elif cur_type == 'AST_ARRAY':
        used_objs = set()
        children = G.get_ordered_ast_child_nodes(node_id)
        if G.get_node_attr(node_id).get('flags:string[]') == 'JS_OBJECT':
            added_obj = G.add_obj_node(node_id, "object")
        else:
            added_obj = G.add_obj_node(node_id, "array")
            G.add_obj_as_prop(prop_name='length', js_type='number',
                value=len(children), ast_node=node_id, parent_obj=added_obj)

        for child in children:
            result = handle_node(G, child, ExtraInfo(extra,
                parent_obj=added_obj))
            # used_objs.update(result.obj_nodes)

        return NodeHandleResult(obj_nodes=[added_obj],
                                used_objs=list(used_objs),
                                callback=get_df_callback(G))

    elif cur_type == 'AST_ARRAY_ELEM':
        if not (extra and extra.parent_obj is not None):
            logger.error("AST_ARRAY_ELEM occurs outside AST_ARRAY")
            return None
        else:
            # should only have two childern
            try:
                value_node, key_node = G.get_ordered_ast_child_nodes(node_id)
            except:
                # TODO: Check what happend here for colorider
                return NodeHandleResult()
                
            key = G.get_name_from_child(key_node)
            if key is not None:
                key = key.strip("'\"")
            else:
                # shouldn't convert it to int
                key = G.get_node_attr(node_id).get('childnum:int')
            if key is None:
                key = wildcard
            handled_value = handle_node(G, value_node, extra)
            value_objs = to_obj_nodes(G, handled_value, node_id)
            # used_objs = list(set(handled_value.used_objs))
            for obj in value_objs:
                G.add_obj_as_prop(key, node_id,
                    parent_obj=extra.parent_obj, tobe_added_obj=obj)
        return NodeHandleResult(obj_nodes=value_objs, # used_objs=used_objs,
            callback=get_df_callback(G))

    elif cur_type == "AST_ENCAPS_LIST":
        # children = G.get_ordered_ast_child_nodes(node_id)
        # used_objs = set()
        # added_obj = G.add_obj_node(ast_node=node_id, js_type='string')
        # for child in children:
        #     handle_res = handle_node(G, child)
        #     used_objs.update(handle_res.obj_nodes)
        #     # used_objs.update(handle_res.used_objs)
        #     for obj in handle_res.obj_nodes:
        #         add_contributes_to(G, [obj], added_obj, 'encaps_list')
        # return NodeHandleResult(obj_nodes=[added_obj], used_objs=list(used_objs),
        #     callback=get_df_callback(G))
        return handle_template(G, node_id, extra)

    elif cur_type == 'AST_VAR' or cur_type == 'AST_NAME' or cur_type == 'AST_CONST':
        return handle_var(G, node_id, side, extra)

    elif cur_type == 'AST_DIM':
        # G.set_node_attr(node_id, ('type', 'AST_PROP'))
        return handle_prop(G, node_id, side, extra)[0]

    elif cur_type == 'AST_PROP':
        return handle_prop(G, node_id, side, extra)[0]

    elif cur_type == 'AST_TOPLEVEL':
        flags = G.get_node_attr(node_id).get('flags:string[]')
        if flags == 'TOPLEVEL_FILE':
            module_exports_objs = run_toplevel_file(G, node_id)
            return NodeHandleResult(obj_nodes=module_exports_objs)
        elif flags == 'TOPLEVEL_CLASS':
            return handle_class(G, node_id, extra)

    elif cur_type in ['AST_FUNC_DECL', 'AST_CLOSURE']:
        obj_nodes = G.get_func_decl_objs_by_ast_node(node_id,
                    scope=G.find_ancestor_scope())
        # print('{} is found to be declared as {} in {}'.format(node_id, obj_nodes, G.find_ancestor_scope()))
        if not obj_nodes:
            obj_nodes = [decl_function(G, node_id)]
        return NodeHandleResult(obj_nodes=obj_nodes)

    elif cur_type == 'AST_CLASS':
        return handle_class(G, node_id, extra)

    elif cur_type == 'AST_METHOD':
        handle_method(G, node_id, extra)

    elif cur_type == 'AST_BINARY_OP':
        left_child, right_child = G.get_ordered_ast_child_nodes(node_id)
        flag = cur_node_attr.get('flags:string[]')
        if flag == 'BINARY_BOOL_OR':
            # TODO: add value check to filter out false values
            handled_left = handle_node(G, left_child, extra)
            handled_right = handle_node(G, right_child, extra)
            now_objs = list(set(to_obj_nodes(G, handled_left, node_id)
                + to_obj_nodes(G, handled_right, node_id)))
            return NodeHandleResult(obj_nodes=now_objs)
        elif flag in ['BINARY_ADD', 'BINARY_SUB']:
            if G.first_pass:
                # return handle_op_by_values(G, node_id, extra)
                return handle_op_simple(G, node_id, extra)
            elif G.auto_exploit:
                return handle_op_by_objs(G, node_id, extra)
            else:
                return handle_op_by_values(G, node_id, extra)
        elif flag in ['BINARY_BOOL_OR', 'BINARY_BOOL_AND', 'BINARY_IS_EQUAL',
            'BINARY_IS_IDENTICAL', 'BINARY_IS_NOT_EQUAL',
            'BINARY_IS_NOT_IDENTICAL', 'BINARY_IS_SMALLER',
            'BINARY_IS_GREATER', 'BINARY_IS_SMALLER_OR_EQUAL',
            'BINARY_IS_GREATER_OR_EQUAL']:
            p, d, t = check_condition(G, node_id, extra)
            if not d:
                return NodeHandleResult(values=[wildcard], 
                                        obj_nodes=[G.true_obj, G.false_obj])
            elif p == 1:
                return NodeHandleResult(obj_nodes=[G.true_obj])
            elif p == 0:
                return NodeHandleResult(obj_nodes=[G.false_obj])
            else:
                return NodeHandleResult(obj_nodes=[G.true_obj, G.false_obj])

    elif cur_type == 'AST_ASSIGN_OP':
        # left_child, right_child = G.get_ordered_ast_child_nodes(node_id)
        # handled_left = handle_node(G, left_child, extra)
        # handled_right = handle_node(G, right_child, extra)
        # # TODO: single wildcard value for multiple inputs
        # added_obj = G.add_obj_node(node_id, value=wildcard)
        # used_objs = []
        # used_objs.extend(to_obj_nodes(G, handled_left, node_id))
        # used_objs.extend(to_obj_nodes(G, handled_right, node_id))
        # used_objs = list(set(used_objs))
        # # for obj in used_objs:
        # #     add_contributes_to(G, [obj], added_obj)
        # add_contributes_to(G, used_objs, added_obj)
        # right_override = NodeHandleResult(obj_nodes=[added_obj],
        #     used_objs=used_objs, callback=get_df_callback(G))
        # return handle_assign(G, node_id, extra, right_override)
        handle_op_by_objs(G, node_id, extra)

    elif cur_type in ['integer', 'double', 'string']:
        js_type = 'string' if cur_type == 'string' else 'number'
        code = G.get_node_attr(node_id).get('code')
        try:
            if cur_type == 'integer' and \
                code.startswith("0x") or code.startswith("0X"):
                    value = int(code, 16)
            elif cur_type == 'integer' and \
                code.startswith("0b") or code.startswith("0B"):
                    value = int(code, 2)
            elif cur_type == 'string':
                if G.get_node_attr(node_id).get('flags:string[]') == 'JS_REGEXP':
                    added_obj = G.add_obj_node(ast_node=node_id,
                                            js_type=None, value=code)
                    G.add_obj_as_prop('__proto__',
                        parent_obj=added_obj, tobe_added_obj=G.regexp_prototype)
                    return NodeHandleResult(obj_nodes=[added_obj])
                else:
                    value = code
            else:
                if code[:2].lower() in ['0b', '0o', '0x']:
                    value = float(int(code, base=0))
                else:
                    value = float(code)
        except ValueError:
            logger.error('ValueError for {} at AST node {}, Line {}'.format(
                    code, node_id, G.get_node_attr(node_id).get('lineno:int')))
            value = wildcard
        assert value is not None
        # added_obj = G.add_obj_node(node_id, js_type, code)
        return NodeHandleResult(values=[value])

    elif cur_type in ['AST_CALL', 'AST_METHOD_CALL', 'AST_NEW']:
        r = handle_call(G, node_id, extra)
        counter = G.get_node_attr(node_id).get('caller_counter')
        if counter is None:
            counter = 0
        G.set_node_attr(node_id, ('caller_exec_counter', counter + 1)) # ?

        # constraint solver
        # if G.solve_from:
        #     arg_list_node = G.get_ordered_ast_child_nodes(node_id)[-1]
        #     arg_list = G.get_ordered_ast_child_nodes(arg_list_node)
        #     handled_arg = handle_node(G, arg_list[0], extra)
        #     logger.log(ATTENTION, 'Constraint solver is solving...')
        #     solution = solver.solve(G, handled_arg.obj_nodes, None,
        #                             contains=(G.solve_mode == 1))
        #     for i, (assertions, results) in enumerate(solution):
        #         logger.debug(f'{sty.ef.inverse}Constraints #{i+1}:{sty.rs.all}')
        #         logger.debug(assertions)      
        #         if results == 'failed':
        #             logger.warning(f'Attempt #{i+1} failed.')
        #             continue
        #         elif results == 'timeout':
        #             logger.warning(f'Attempt #{i+1} timed out.')
        #             continue
        #         logger.debug(f'{sty.ef.inverse}Results #{i+1}:{sty.rs.all}')
        #         if results:
        #             for k, (name, v) in results.items():
        #                 logger.debug(f'{name}({k}) = {v}')
        #         else:
        #             logger.debug('No result.')
        #     input('Solving finished, press enter to continue...')
        #     G.solve_from = None
        return NodeHandleResult(obj_nodes=r.obj_nodes, used_objs=r.used_objs,
            values=r.values, value_sources=r.value_sources,
            ast_node=node_id, callback=get_df_callback(G))

    elif cur_type == 'AST_RETURN':
        returned_exp = G.get_ordered_ast_child_nodes(node_id)[0]
        results = handle_node(G, returned_exp, extra)
        # print(f'Returns: {results} -> {G.function_returns[G.find_ancestor_scope()]}')
        obj_nodes = to_obj_nodes(G, results, node_id)
        func_scope = G.find_ancestor_scope()
        # add handled obj nodes to the function's return value dict
        G.function_returns[func_scope].extend(obj_nodes)
        func_ast = G.get_successors(func_scope, edge_type='SCOPE_TO_AST')[0]
        exit_node = G.get_successors(func_ast, edge_type='EXIT')[0]
        # add a CF edge from the current statement to the function's
        # EXIT node
        G.add_edge_if_not_exist(node_id, exit_node, {'type:TYPE': 'FLOWS_TO'})
        # return results
        return NodeHandleResult(ast_node=node_id, obj_nodes=obj_nodes,
            used_objs=list(chain(*results.value_sources)),
            callback=get_df_callback(G))
    
    elif cur_type == 'AST_IF':
        # lineno = G.get_node_attr(node_id).get('lineno:int')
        stmt_id = "If" + node_id + "-" + get_random_hex()
        if_elems = G.get_ordered_ast_child_nodes(node_id)
        branches = extra.branches
        parent_branch = branches.get_last_choice_tag()
        # NOTE: two branches (JavaScript)
        if_elem = if_elems[0]
        condition, body = G.get_ordered_ast_child_nodes(if_elem)
        # condition = debug_extra.get('condition') or condition
        last_stmts = []
        # check condition
        if G.first_pass:
            # we don't check condition in the first pass
            check_condition(G, condition, extra) # ensure control flow
            possibility, deterministic, tag = 0.5, False, None
        else:
            possibility, deterministic, tag = \
                check_condition(G, condition, extra)
        if deterministic and possibility == 1:
            # if the condition is surely true
            G.last_stmts = [node_id]
            simurun_block(G, body, G.cur_scope, branches)
            last_stmts.extend(G.last_stmts)
        elif (G.single_branch and possibility != 0) or len(if_elems) == 1:
            tag0 = BranchTag(point=stmt_id, branch=str(0))
            tag1 = BranchTag(point=stmt_id, branch=str(1))
            G.affected_name_nodes.append(set())
            if len(if_elems) == 2:
                else_elem = if_elems[1]
                else_body = G.get_ordered_ast_child_nodes(else_elem)[-1]
                if_dist = G.get_node_attr(body).get('distance_to_goal')
                else_dist = G.get_node_attr(else_body).get('distance_to_goal')
                logger.debug(f'Distance from "if" to goal: {if_dist}\n'
                             f'Distance from "else" to goal: {else_dist}')
                if if_dist is not None and else_dist is not None and \
                        if_dist > else_dist:
                    G.last_stmts = [node_id]
                    simurun_block(G, else_body, G.cur_scope, branches+[tag1])
                    last_stmts.extend(G.last_stmts)
                    G.last_stmts = [node_id]
                    simurun_block(G, body, G.cur_scope, branches+[tag0])
                    last_stmts.extend(G.last_stmts)
                else:
                    G.last_stmts = [node_id]
                    simurun_block(G, body, G.cur_scope, branches+[tag0])
                    last_stmts.extend(G.last_stmts)
                    G.last_stmts = [node_id]
                    simurun_block(G, else_body, G.cur_scope, branches+[tag1])
                    last_stmts.extend(G.last_stmts)
            else:
                G.last_stmts = [node_id]
                simurun_block(G, body, G.cur_scope, branches+[tag0])
                last_stmts.extend(G.last_stmts)
                # add the if statement if there is only one branch
                last_stmts.append(node_id)
            if not G.single_branch:
                merge(G, stmt_id, 2, parent_branch)
            if len(G.affected_name_nodes) > 1:
                G.affected_name_nodes[-2].update(G.affected_name_nodes[-1])
            G.affected_name_nodes.pop()
        elif not deterministic or possibility is None or 0 < possibility < 1:
            # if the condition is unsure
            tag0 = BranchTag(point=stmt_id, branch=str(0))
            tag1 = BranchTag(point=stmt_id, branch=str(1))
            G.affected_name_nodes.append(set())
            else_elem = if_elems[1]
            else_body = G.get_ordered_ast_child_nodes(else_elem)[-1]
            if_dist = G.get_node_attr(body).get('distance_to_goal')
            else_dist = G.get_node_attr(else_body).get('distance_to_goal')
            logger.debug(f'Distance from "if" to goal: {if_dist}\n'
                            f'Distance from "else" to goal: {else_dist}')
            if if_dist is not None and else_dist is not None and \
                if_dist > else_dist:
                G.last_stmts = [node_id]
                simurun_block(G, body, G.cur_scope, branches+[tag0])
                last_stmts.extend(G.last_stmts)
                G.last_stmts = [node_id]
                simurun_block(G, else_body, G.cur_scope, branches+[tag1])
                last_stmts.extend(G.last_stmts)
            else:
                G.last_stmts = [node_id]
                simurun_block(G, else_body, G.cur_scope, branches+[tag0])
                last_stmts.extend(G.last_stmts)
                G.last_stmts = [node_id]
                simurun_block(G, body, G.cur_scope, branches+[tag1])
                last_stmts.extend(G.last_stmts)
            if not G.single_branch:
                merge(G, stmt_id, 2, parent_branch)
            if len(G.affected_name_nodes) > 1:
                G.affected_name_nodes[-2].update(G.affected_name_nodes[-1])
            G.affected_name_nodes.pop()
        else:
            # if the condition is surely false
            if len(if_elems) == 2:
                else_elem = if_elems[1]
                else_body = G.get_ordered_ast_child_nodes(else_elem)[-1]
                G.last_stmts = [node_id]
                simurun_block(G, else_body, G.cur_scope, branches)
                last_stmts.extend(G.last_stmts)
        G.last_stmts = last_stmts
        return NodeHandleResult()
    
    elif cur_type == 'AST_SWITCH':
        condition, switch_list = G.get_ordered_ast_child_nodes(node_id)
        G.add_edge_if_not_exist(node_id, switch_list, {"type:TYPE": "FLOWS_TO"})
        result = handle_node(G, condition, extra)
        handle_node(G, switch_list, ExtraInfo(extra, switch_var=result))
        return result

    elif cur_type == 'AST_SWITCH_LIST':
        stmt_id = "Switch" + node_id
        branches = extra.branches
        parent_branch = branches.get_last_choice_tag()
        cases = G.get_ordered_ast_child_nodes(node_id)
        default_is_deterministic = True
        last_stmts = []
        G.affected_name_nodes.append(set())
        for i, case in enumerate(cases):
            G.add_edge_if_not_exist(node_id, case, {"type:TYPE": "FLOWS_TO"})
            branch_tag = BranchTag(point=stmt_id, branch=str(i))
            test, body = G.get_ordered_ast_child_nodes(case)
            if G.get_node_attr(test).get('type') == 'NULL': # default
                if default_is_deterministic or G.single_branch:
                    G.last_stmts = [case]
                    simurun_block(G, body, G.cur_scope, branches,
                                  block_scope=False)
                    last_stmts.extend(G.last_stmts)
                else:
                    # not deterministic
                    G.last_stmts = [case]
                    simurun_block(G, body, G.cur_scope, branches+[branch_tag],
                                  block_scope=False)
                    last_stmts.extend(G.last_stmts)
                continue
            if G.first_pass:
                p, d = 0.5, False
                default_is_deterministic = False
            else:
                # handle_node(G, test, extra)
                G.last_stmts = [case]
                p, d = check_switch_var(G, test, extra)
                # print('check result =', p, d)
            if d and p == 1:
                G.last_stmts = [case]
                simurun_block(G, body, G.cur_scope, branches,
                            block_scope=False)
                last_stmts.extend(G.last_stmts)
                break
            elif not d or 0 < p < 1:
                G.last_stmts = [case]
                simurun_block(G, body, G.cur_scope, branches+[branch_tag],
                            block_scope=False)
                last_stmts.extend(G.last_stmts)
                default_is_deterministic = False
            else:
                continue
        if not G.single_branch:
            merge(G, stmt_id, len(cases), parent_branch)
        if len(G.affected_name_nodes) > 1:
            G.affected_name_nodes[-2].update(G.affected_name_nodes[-1])
        G.affected_name_nodes.pop()
        G.last_stmts = last_stmts

    elif cur_type == 'AST_CONDITIONAL':
        test, consequent, alternate = G.get_ordered_ast_child_nodes(node_id)
        logger.debug(f'Ternary operator: {test} ? {consequent} : {alternate}')
        possibility, deterministic, tag = check_condition(G, test, extra)
        if deterministic and possibility == 1:
            return handle_node(G, consequent, extra)
        elif deterministic and possibility == 0:
            return handle_node(G, alternate, extra)
        else:
            # h1 = handle_node(G, consequent, extra)
            # h2 = handle_node(G, alternate, extra)
            # return NodeHandleResult(obj_nodes=h1.obj_nodes+h2.obj_nodes,
            #     name_nodes=h1.name_nodes+h2.name_nodes, ast_node=node_id,
            #     values=h1.values+h2.values,
            #     value_sources=h1.value_sources+h2.value_sources,
            #     callback=get_df_callback(G))
            h1 = handle_node(G, consequent, extra)
            h2 = handle_node(G, alternate, extra)
            # h1_tainted = False
            # for obj in h1.obj_nodes:
            #     if G.get_node_attr(obj).get('tainted'):
            #         h1_tainted = True
            #         break
            h2_tainted = False
            for obj in h2.obj_nodes:
                if G.get_node_attr(obj).get('tainted'):
                    h2_tainted = True
                    break
            if G.first_pass or (len(h1.obj_nodes) <= 100 and len(h2.obj_nodes) <= 100):
                return NodeHandleResult(obj_nodes=h1.obj_nodes+h2.obj_nodes,
                    name_nodes=h1.name_nodes+h2.name_nodes, ast_node=node_id,
                    values=h1.values+h2.values,
                    value_sources=h1.value_sources+h2.value_sources,
                    callback=get_df_callback(G))
            elif h2_tainted:
                return h2
            else:
                return h1

    elif cur_type == 'AST_EXPR_LIST':
        result = NodeHandleResult()
        for child in G.get_ordered_ast_child_nodes(node_id):
            result = handle_node(G, child, extra)
        return result

    elif cur_type == 'AST_FOR':
        init, cond, inc, body = None, None, None, None
        try:
            init, cond, inc, body = G.get_ordered_ast_child_nodes(node_id)[:4]
        except ValueError as e:
            for n in G.get_ordered_ast_child_nodes(node_id):
                logger.error(n, G.get_node_attr(n))
                return None
        cond = G.get_ordered_ast_child_nodes(cond)[0]
        # switch scopes
        parent_scope = G.cur_scope
        G.cur_scope = G.add_scope('BLOCK_SCOPE', decl_ast=body,
                      scope_name=G.scope_counter.gets(f'Block{body}'))
        G.scope_stack.append(G.cur_scope)
        result = handle_node(G, init, extra) # init loop variables
        counter = 0
        # max_count = 1 if G.first_pass else 3
        max_count = 1 if G.first_pass else G.call_limit
        while True:
            # check increment to determine loop variables
            # FIXED: d should be updated every iteration
            d = peek_variables(G, ast_node=inc, extra=extra)
            logger.debug('For loop variables:')
            for name, obj_nodes in d.items():
                logger.debug(sty.ef.i + name + sty.rs.all + ': ' +
                    ', '.join([(sty.fg.green+'{}'+sty.rs.all+' {}').format(obj,
                    val_to_str(G.get_node_attr(obj).get('code'))) for obj in obj_nodes]))

            # check if the condition is met
            check_result, deterministic, tag = check_condition(G, cond, extra)
            # avoid infinite loop
            if (not deterministic and counter >= max_count) or \
                    check_result == 0 or (counter > 0 and G.first_pass):
                logger.debug('For loop {} finished'.format(node_id))
                break
            G.last_stmts = [node_id]
            simurun_block(G, body, branches=extra.branches) # run the body
            result = handle_node(G, inc, extra) # do the inc
            counter += 1
        # switch back the scope
        G.cur_scope = parent_scope
        G.scope_stack.pop()

    elif cur_type == 'AST_FOREACH':
        if G.get_node_attr(node_id).get('flags:string[]') == 'JS_FOR_IN':
            if G.first_pass:
                handle_for_in_fast(G, node_id, extra)
            else:
                handle_for_in(G, node_id, extra)
        elif G.get_node_attr(node_id).get('flags:string[]') == 'JS_FOR_OF':
            if G.first_pass:
                handle_for_of_fast(G, node_id, extra)
            else:
                handle_for_of(G, node_id, extra)

    elif cur_type == 'AST_WHILE':
        test, body = None, None
        try:
            test, body = G.get_ordered_ast_child_nodes(node_id)[:2]
        except ValueError as e:
            for n in G.get_ordered_ast_child_nodes(node_id):
                logger.error(n, G.get_node_attr(n))
        if test is None or body is None:
            return NodeHandleResult()
        # switch scopes
        parent_scope = G.cur_scope
        G.cur_scope = G.add_scope('BLOCK_SCOPE', decl_ast=body,
                      scope_name=G.scope_counter.gets(f'Block{body}'))
        G.scope_stack.append(G.cur_scope)
        counter = 0
        while True:
            # check if the condition is met
            check_result, deterministic, tag = check_condition(G, test, extra)
            logger.debug('While loop condition {} result: {} {}'.format(
                sty.ef.i + G.get_node_attr(test).get('code') + sty.rs.all,
                check_result, deterministic))
            # avoid infinite loop
            if (not deterministic and counter > G.call_limit) or check_result == 0 or \
                    counter > 10 or G.first_pass:
            # if (not deterministic and counter > 3) or check_result == 0 or \
            #         counter > 10 or (G.two_pass and G.first_pass):
                logger.debug('For loop {} finished'.format(node_id))
                break
            G.last_stmts = [node_id]
            simurun_block(G, body, branches=extra.branches) # run the body
            counter += 1
        # switch back the scope
        G.cur_scope = parent_scope
        G.scope_stack.pop()

    elif cur_type in ['AST_PRE_INC', 'AST_POST_INC', 'AST_PRE_DEC', 'AST_POST_DEC']:
        child = G.get_ordered_ast_child_nodes(node_id)[0]
        handled_child = handle_node(G, child, extra)
        returned_values = []
        sources = []
        for name_node in handled_child.name_nodes:
            updated_objs = []
            for obj in G.get_objs_by_name_node(name_node, extra.branches):
                v = G.get_node_attr(obj).get('code')
                if v == wildcard or v is None:
                    continue
                n = val_to_float(v)
                if 'POST' in cur_type:
                    returned_values.append(n)
                else:
                    if 'INC' in cur_type:
                        returned_values.append(n + 1)
                    else:
                        returned_values.append(n - 1)
                sources.append([obj])
                if 'INC' in cur_type:
                    new_value = n + 1
                else:
                    new_value = n - 1
                updated_objs.append(G.add_obj_node(
                        G.get_obj_def_ast_node(obj), 'number', new_value))
            G.assign_obj_nodes_to_name_node(name_node, updated_objs,
                branches=extra.branches)
        returned_values, sources = combine_values(returned_values, sources)
        return NodeHandleResult(values=returned_values, value_sources=sources)

    elif cur_type == 'AST_UNARY_OP':
        child = G.get_ordered_ast_child_nodes(node_id)[0]
        handled = handle_node(G, child, extra)
        values, sources, _ = to_values(G, handled)
        new_values = []
        for v in values:
            if v == wildcard or v is None:
                new_values.append(v)
                continue
            v = val_to_float(v)
            if v != float('nan') and G.get_node_attr(node_id).get(
                    'flags:string[]') == 'UNARY_MINUS':
                new_values.append(-v)
            else:
                new_values.append(v)
        logger.debug(f'New values: {new_values}')
        return NodeHandleResult(values=new_values, value_sources=sources)

    # handle registered functions      # deprecated
    # if "HAVE_FUNC" in cur_node_attr:
    #     for func_decl_id in registered_func[node_id]:
    #         logger.info(sty.ef.inverse + sty.fg.red + "RUN register {}".format(func_decl_id) + sty.rs.all)
    #         handle_node(G, func_decl_id, extra)

    return NodeHandleResult()

def decl_vars_and_funcs(G, ast_node, var=True, func=True):
    # pre-declare variables and functions
    func_scope = G.find_ancestor_scope()
    children = G.get_ordered_ast_child_nodes(ast_node)
    for child in children:
        node_type = G.get_node_attr(child)['type']
        if var and node_type == 'AST_VAR' and \
            G.get_node_attr(child)['flags:string[]'] == 'JS_DECL_VAR':
            # var a;
            name = G.get_name_from_child(child)
            if G.get_name_node(name, scope=func_scope,
                               follow_scope_chain=False) is None:
                G.add_obj_to_scope(name=name, scope=func_scope,
                                   tobe_added_obj=G.undefined_obj)
        elif var and node_type == 'AST_ASSIGN':
            # var a = ...;
            children = G.get_ordered_ast_child_nodes(child)
            if G.get_node_attr(children[0])['type'] == 'AST_VAR' and \
                G.get_node_attr(children[0])['flags:string[]'] == 'JS_DECL_VAR':
                name = G.get_name_from_child(children[0])
                # if name node does not exist, add a name node in the scope
                # and assign it to the undefined object
                if G.get_name_node(name, scope=func_scope,
                                   follow_scope_chain=False) is None:
                    G.add_obj_to_scope(name=name, scope=func_scope,
                                       tobe_added_obj=G.undefined_obj)
                else:
                    pass
        elif func and node_type == 'AST_FUNC_DECL':
            func_name = G.get_name_from_child(child)
            func_obj = decl_function(G, child, obj_parent_scope=func_scope)
        # elif node_type == 'AST_STMT_LIST':
        #     decl_vars_and_funcs(G, child, var=var, func=func)
        elif node_type in ['AST_IF', 'AST_IF_ELEM', 'AST_FOR', 'AST_FOREACH',
            'AST_WHILE', 'AST_SWITCH', 'AST_SWITCH_CASE', 'AST_EXPR_LIST',
            'AST_TRY', 'AST_CATCH_LIST', 'AST_CATCH', 'AST_STMT_LIST']:
            decl_vars_and_funcs(G, child, var=var, func=False)

def simurun_function(G, func_ast, branches=None, block_scope=True,
    caller_ast=None):
    """
    Simurun a function by running its body.
    """

    if branches is None or G.single_branch:
        # create an instance of BranchTagContainer every time,
        # don't use default argument
        branches = BranchTagContainer()

    func_objs = G.get_func_decl_objs_by_ast_node(func_ast)
    func_obj = func_objs[0] if func_objs else '?'
    func_name = G.get_node_attr(func_obj).get('name') if func_objs else '?'
    entry_node = G.get_successors(func_ast, edge_type='ENTRY')[0]

    # rough CF run
    if G.two_pass:
        builtin_path = os.path.normpath(os.path.abspath(__file__)
                                                + '../../../builtin_packages')
        # file_path = G.get_cur_file_path()
        file_path = G.get_node_file_path(func_ast)
        if G.first_pass:
            pass
            # moved to call_func_obj
            # attrs = G.get_node_attr(func_ast)
            # returned_objs = attrs.get('stored_returned_objs')
            # used_objs = attrs.get('stored_used_objs')
            # if returned_objs is not None and used_objs is not None and \
            #         not (file_path and file_path.startswith(builtin_path)): # not a modeled function
            #     logger.info((sty.ef.inverse + sty.fg.green + 
            #         'FUNCTION {} {} SKIPPED by rough run, DECL OBJ {}'
            #         + sty.rs.all).format(
            #             func_ast, func_name or '{anonymous}', func_obj))
            #     return returned_objs, used_objs
        else: # second run
            if not G.dont_quit and entry_node not in G.possible_cf_nodes and \
                    file_path and not file_path.startswith(builtin_path): # not a modeled function
                logger.info((sty.ef.inverse + sty.fg.green + 
                    'FUNCTION {} {} SKIPPED by rough CF filtering, DECL OBJ {}'
                    + sty.rs.all).format(
                        func_ast, func_name or '{anonymous}', func_obj))
                return [], []

    counter = G.get_node_attr(func_ast).get('exec_counter', 0)
    if counter > G.exec_counter_limit:
        return [], []

    if caller_ast is not None:
        if G.caller_counter[caller_ast] >= G.call_limit:
            logger.warning(f'{caller_ast}: Function {func_ast} in call stack '
                    f'{G.caller_counter[caller_ast]} times, skip simulating')
            return None, None # don't change this to [], []
                              # we need to distinguish skipped functions
        else:
            G.caller_counter[caller_ast] += 1
            G.caller_stack.append(caller_ast)

    logger.info(sty.ef.inverse + sty.fg.green +
        "FUNCTION {} {} STARTS, SCOPE {}, DECL OBJ {}, this OBJs {}, branches {}"
        .format(func_ast, func_name or '{anonymous}',
        G.cur_scope, func_obj, G.cur_objs,
        branches) + sty.rs.all)
    scope_chain = [G.cur_scope]
    _scope = G.cur_scope
    while _scope != G.BASE_SCOPE:
        edges = G.get_in_edges(_scope, edge_type='PARENT_SCOPE_OF')
        if edges:
            _scope = edges[0][0]
        else:
            break
        scope_chain.append(_scope)
    logger.info(sty.fg.green + 'Scope chain: ' + str(scope_chain) + sty.rs.all)
    returned_objs, used_objs = [], []
    # if G.two_pass and not G.first_pass and G.cf_guided: # abandoned
    #     cfg_traverse(G, entry_node, extra=ExtraInfo(branches=branches))
    #     returned_objs = G.function_returns[G.find_ancestor_scope()]
    # else:
    for child in G.get_child_nodes(func_ast, child_type='AST_STMT_LIST'):
        G.last_stmts = [entry_node]
        returned_objs, used_objs = simurun_block(G, child,
            parent_scope=G.cur_scope, branches=branches,
            block_scope=block_scope, decl_var=True)
        break

    if caller_ast is not None:
        G.caller_counter[caller_ast] -= 1
        G.caller_stack.pop()

    if G.first_pass:
        G.set_node_attr(func_ast, ('stored_returned_objs', returned_objs))
        G.set_node_attr(func_ast, ('stored_used_objs', used_objs))

    exit_node = G.get_successors(func_ast, edge_type='EXIT')[0]
    for last_stmt in G.last_stmts:
        G.add_edge_if_not_exist(
            last_stmt, exit_node, {"type:TYPE": "FLOWS_TO"})
    G.last_stmts = [exit_node]

    return returned_objs, used_objs

def simurun_block(G, ast_node, parent_scope=None, branches=None,
    block_scope=True, decl_var=False):
    """
    Simurun a block by running its statements one by one.
    A block is a BlockStatement in JavaScript,
    or an AST_STMT_LIST in PHP.
    """
    if branches is None or G.single_branch:
        branches = BranchTagContainer()
    if not G.dont_quit and (G.rough_call_dist and 
            G.get_node_attr(ast_node).get('distance_to_goal') is None):
        logger.warning(f'Block {ast_node} exits because of infinite distance')
        logger.warning(f'Call stack: {G.call_stack}')
        return [], []
    builtin_path = os.path.normpath(os.path.abspath(__file__) + '../../../builtin_packages')
    file_path = G.get_cur_file_path()
    prev_dont_quit = G.dont_quit
    if (file_path is None or # why?
            file_path.startswith(builtin_path)): # modeled built-in modules
        G.dont_quit = 'built-in'
    if G.two_pass and not G.first_pass:
        if not G.dont_quit and ast_node not in G.possible_cf_nodes:
            logger.log(ATTENTION, 'BLOCK {} SKIPPED by rough CF filtering'
                        .format(ast_node, G.cur_scope))
            G.dont_quit = prev_dont_quit
            return [], []

    returned_objs = set()
    used_objs = set()
    if parent_scope == None:
        parent_scope = G.cur_scope
    if block_scope:
        G.cur_scope = \
            G.add_scope('BLOCK_SCOPE', decl_ast=ast_node,
                        scope_name=G.scope_counter.gets(f'Block{ast_node}'))
    G.scope_stack.append(G.cur_scope)
    logger.log(ATTENTION, 'BLOCK {} STARTS, SCOPE {}'.format(ast_node, G.cur_scope))
    decl_vars_and_funcs(G, ast_node, var=decl_var)
    stmts = G.get_ordered_ast_child_nodes(ast_node)
    # control flows
    for last_stmt in G.last_stmts:
        G.add_edge_if_not_exist(last_stmt, ast_node, {'type:TYPE': 'FLOWS_TO'})
    G.last_stmts = [ast_node]
    # simulate statements
    for stmt in stmts:
        if G.two_pass and not G.first_pass:
            # print('stmt', stmt, G.dont_quit, stmt in G.possible_cf_nodes)
            if not G.dont_quit and stmt not in G.possible_cf_nodes:
                logger.log(ATTENTION, 'Statement {} (Line {}) SKIPPED by rough CF filtering'
                        .format(stmt, G.get_node_attr(stmt).get('lineno:int'), G.cur_scope))
                continue

        # build control flows from the previous statement to the current one
        for last_stmt in G.last_stmts:
            G.add_edge_if_not_exist(last_stmt, stmt, {'type:TYPE': 'FLOWS_TO'})
        G.last_stmts = [stmt]
        G.cur_stmt = stmt
        # Anything starting from a statement on a CF path is considered
        # on the CF path. In other words, you cannot skip anything when
        # recursively handle this statement.
        # If statements and Switch statments (but not If elements and
        # Switch cases) are exceptions.
        _prev_dont_quit = G.dont_quit
        if (stmt in G.possible_cf_nodes and # avoid going all the way deep from stdin
                G.get_node_attr(stmt).get('type') not in ['AST_IF', 'AST_SWITCH']):
            G.dont_quit = f'go deep from {stmt}'
        handled_res = handle_node(G, stmt, ExtraInfo(branches=branches))
        # to_obj_nodes(G, handled_res, stmt) # for data flow?
        G.dont_quit = _prev_dont_quit

        if G.finished or G.time_limit_reached:
            break

        # build control flows from other location (previous statment,
        # EXIT nodes of other functions, etc.) to the current statement
        # print(stmt, G.get_node_attr(stmt).get('type'), G.last_stmts)
        # if G.last_stmts != [stmt]:
        #     for last_stmt in G.last_stmts:
        #         G.add_edge(last_stmt, stmt, {'type:TYPE': 'FLOWS_TO'})
        # we never build control flows from a return statement to any
        # other statement
        if G.get_node_attr(stmt).get('type') == 'AST_RETURN':
            G.last_stmts = []
        # if G.get_node_attr(stmt).get('type') != 'AST_RETURN':
        #     G.last_stmts = [stmt]

    returned_objs = G.function_returns[G.find_ancestor_scope()]
    
    if block_scope:
        G.cur_scope = parent_scope
    G.scope_stack.pop()

    if (file_path is None or # why?
            file_path.startswith(builtin_path)): # modeled built-in modules
        G.dont_quit = prev_dont_quit # restore
    
    exits = G.get_successors(ast_node, edge_type='EXIT')
    assert len(exits) <= 1
    if not exits:
        exits = [G.add_exit_node(parent=ast_node)]
    for last_stmt in G.last_stmts:
        G.add_edge_if_not_exist(last_stmt, exits[0], {'type:TYPE': 'FLOWS_TO'})
    G.last_stmts = exits
    
    return list(returned_objs), list(used_objs)

def call_func_obj(G: Graph, func_obj, _args=[], _this=None, extra=None,
        call_ast=None, is_new=False, has_branches=False, stmt_id='Unknown',
        func_name=None, mark_fake_args=False, python_callback=None,
        branch_num=-1, returned_values=None, returned_value_sources=None,
        exit_nodes=None, fake_returned_objs=None, fake_created_objs=None,
        dont_skip=False, promise_related=False):
    # copy "this" and "args" references
    # because we may edit them later
    # and we want to keep original "this" and "args"
    # NOTE: done by arugment passing (_this=this, _args=args)

    call_stack_item = '{}'.format(func_name)
    if G.call_stack.count(call_stack_item) > 20:
        return [], [], [], False, False
    G.call_stack.append(call_stack_item)

    # create default arguments (These arguments are used by call_function to
    # return some values to the outside of the loop. They are useless if
    # call_func_obj is called elsewhere. fake_returned_objs and
    # fake_created_objs should only contain one item. We use a list because
    # we want to pass the item back to call_function, i.e. to modify the
    # reference.)
    if returned_values is None:
        returned_values = []
    if returned_value_sources is None:
        returned_value_sources = []
    if exit_nodes is None:
        exit_nodes = set()
    if fake_returned_objs is None:
        fake_returned_objs = []
    if fake_created_objs is None:
        fake_created_objs = []

    if G.get_node_attr(func_obj).get('unresolved') == True:
        if G.cur_func_call is None or G.cur_func_call[2] is None or (
                G.cur_func_call[2] < call_ast):
            # If there is no Current Function,
            # or the Current Function was put into the stack by unknown reason,
            # or the Current Fucntion is not stuck at the same function call
            # because of which the Current Function was put into the stack,
            # we consider the function call not yet resolved. We put the
            # Current Function back to the stack and run other functions first.
            # Then we rerun this function later.
            cur_file_path = G.file_stack[-1] if G.file_stack else None
            new_vector = (G.cur_func_call[0], G.cur_func_call[1], call_ast, G.cur_func_call[3], G.cur_func_call[4], cur_file_path, 1)
            if new_vector in reversed(G.stack1): # avoid duplicated entries
                logger.warning('Vector {} already in stack 1. Call stack: {}'
                    .format(new_vector, G.call_stack))
            else:
                G.stack1.append(new_vector)
            G.rerun_counter += 1
            G.finished = True
            if (call_ast is not None and G.cur_func_call[2] is not None
                    and G.cur_func_call[2] < call_ast):
                # This means the last stuck point (function call) can be
                # dynamically resolved.
                try:
                    G.dynamic_calls.add(G.cur_func_call[2])
                    G.unresolvable_calls.remove(G.cur_func_call[2])
                except KeyError:
                    pass
            G.call_stack.pop()
            return [], [], [], False, False
        else:
            # 
            if call_ast is not None:
                G.unresolvable_calls.add(call_ast)
    # else:
    #     if call_ast is not None:
    #         G.static_calls.add(call_ast)
    # if call_ast is not None:
    #     G.total_calls.add(call_ast)
    
    if extra is None:
        extra = ExtraInfo()
    branches = extra.branches
    parent_branch = branches.get_last_choice_tag()

    # process arguments
    callback_functions = set() # only for dummy functions
    for arg in _args:
        # add callback functions
        for obj in arg.obj_nodes:
            if G.get_node_attr(obj).get('type') == 'function':
                callback_functions.add(obj)
    callback_functions = list(callback_functions)

    # bound functions (bind)
    func_obj_attrs = G.get_node_attr(func_obj)
    if func_obj_attrs.get('target_func'):
        _this = func_obj_attrs.get('bound_this')
        logger.log(ATTENTION, 'Bound function found ({}->{}), this={}'.format(func_obj_attrs.get('target_func'), func_obj, _this.obj_nodes))
        if func_obj_attrs.get('bound_args') is not None:
            _args = func_obj_attrs.get('bound_args')
        func_obj = func_obj_attrs.get('target_func')
    if not _this and func_obj_attrs.get('parent_scope_this'):
        _this = NodeHandleResult(
            obj_nodes=func_obj_attrs.get('parent_scope_this'))
    
    # pass arguments' used objects to the function call
    # for arg in _args:
    #     used_objs.update(arg.used_objs)

    if func_obj in G.internal_objs.values():
        logger.warning('Error: Trying to run an internal obj {} {}'
            ', skipped'.format(func_obj, G.inv_internal_objs[func_obj]))
        G.call_stack.pop()
        return [], [], [], False, False
    func_run = True
    func_skipped = False

    # if branches exist, add a new branch tag to the list
    if has_branches and not G.single_branch:
        next_branches = branches+[BranchTag(point=stmt_id, branch=branch_num)]
    else:
        next_branches = branches

    branch_returned_objs = []
    branch_created_objs = []
    branch_used_objs = []
    func_ast = G.get_obj_def_ast_node(func_obj, aim_type='function')
    if func_ast is not None and G.get_node_attr(func_ast).get('type') not in [
            'AST_FUNC_DECL', 'AST_CLOSURE', 'AST_METHOD', 'AST_TOPLEVEL']:
        func_ast = None
    # check if python function exists
    python_func = G.get_node_attr(func_obj).get('pythonfunc')
    if python_func: # special Python function
        if is_new:
            if func_obj in G.builtin_constructors:
                logger.log(ATTENTION, f'Running Python function {func_obj} {python_func}...')
                try:
                    h = python_func(G, call_ast, ExtraInfo(extra,
                        branches=next_branches), _this, *_args)
                    branch_created_objs.extend(h.obj_nodes)
                    branch_used_objs = h.used_objs
                except TypeError as e:
                    logger.error(tb.format_exc())
            else:
                logger.error(f'Error: try to new Python function {func_obj} {python_func}...')
                G.call_stack.pop()
                return [], [], [], False, False
        else:
            logger.log(ATTENTION, f'Running Python function {func_obj} {python_func}...')
            try:
                h = python_func(G, call_ast,
                    ExtraInfo(extra, branches=next_branches), _this, *_args)
                branch_returned_objs = h.obj_nodes
                # the obj_nodes may be node list
                if type(branch_returned_objs) != list:
                    branch_returned_objs = [branch_returned_objs]
                branch_used_objs = h.used_objs
                returned_values.extend(h.values)
                returned_value_sources.extend(h.value_sources)
            except (TypeError, re.error) as e:
                logger.error(tb.format_exc())

        if func_ast:
            # print('h =', h, _args)
            # print('func ast', func_ast, branch_returned_objs, branch_used_objs)
            body = G.get_child_nodes(func_ast, child_type='AST_STMT_LIST')[0]
            dummy_stmt = list(G.get_child_nodes(body, edge_type='PARENT_OF'))[0]
            NodeHandleResult(ast_node=dummy_stmt,
                obj_nodes=branch_created_objs if is_new else branch_returned_objs,
                used_objs=branch_used_objs,
                callback=get_df_callback(G, ast_node=dummy_stmt if G.new_trace_rule else None))
            # branch_used_objs = []

    else: # JS function in AST
        flag = False
        # first pass (coarse-grained)
        if G.first_pass and func_ast is not None:
        # and not is_new:
            builtin_path = os.path.normpath(os.path.abspath(__file__) + '../../../builtin_packages')
            file_path = G.get_node_file_path(func_ast)
            # print('func obj:', func_obj, 'ast:', func_ast)
            attrs = G.get_node_attr(func_ast)
            returned_objs = attrs.get('stored_returned_objs')
            created_objs = attrs.get('stored_created_objs', [])
            used_objs = attrs.get('stored_used_objs')
            # print(returned_objs, created_objs, used_objs, file_path, builtin_path)
            # print(returned_objs is not None, used_objs is not None ,
            #         file_path is not None,
            #         file_path and not file_path.startswith(builtin_path))
            if (not (file_path and file_path.startswith(builtin_path))
                    # not a modeled function
                    and G.get_node_attr(func_ast).get('labels:label')
                    != 'Artificial_AST' # not a dummy function
                    and not dont_skip): # not rerun
                if returned_objs is not None and used_objs is not None:
                    logger.info((sty.ef.inverse + sty.fg.green + 
                        'FUNCTION {} {} SKIPPED by rough run, DECL OBJ {}'
                        + sty.rs.all).format(
                            func_ast, func_name or '{anonymous}', func_obj))
                    flag = True
                    # return returned_objs, [], used_objs, False, False
                    branch_returned_objs = returned_objs
                    branch_created_objs = created_objs        
                    logger.debug('saved returned objs {}, created objs {}'
                        .format(returned_objs, created_objs))           
                    # branch_returned_objs = [
                    #     G.copy_obj(obj, deep=True) for obj in returned_objs]
                    # branch_created_objs = [
                    #     G.copy_obj(obj, deep=True) for obj in created_objs]   
                    # doesn't matter because we don't create data flows in the first pass
                    branch_used_objs = used_objs
                    func_run = False
                    func_skipped = True
                # elif not dont_skip:
                else:
                    # G.func_call_queue.put((float('inf'), get_random_hex(),
                    #     func_obj, _this, _args))
                    logger.info((sty.ef.inverse + sty.fg.green + 
                        'FUNCTION {} {} returned as unresolved, DECL OBJ {}'
                        + sty.rs.all).format(
                            func_ast, func_name or '{anonymous}', func_obj))
                    # print(dont_skip)
                    obj = G.add_obj_node(js_type=None,value=wildcard)
                    G.set_node_attr(obj, ('unresolved', True))
                    G.set_node_attr(obj, ('how_to_resolve', (func_obj, func_name, _args, _this, None)))
                    branch_returned_objs = [obj]
                    branch_created_objs = [obj]
                    for arg in _args:
                        branch_used_objs.extend(to_obj_nodes(G, arg, call_ast))
                    flag = True
                    func_run = False
                    func_skipped = True

        # callback functions in arguments (function pointers)
        if G.first_pass and flag and (G.get_node_attr(func_ast)
                .get('labels:label') != 'Artificial_AST'): # except dummy functions
            add_saved_cf(G, func_ast, call_ast, _args, branches)
                
        if not flag: # second pass (fine-grained)
            # if AST cannot be found, create AST
            if func_ast is None or G.get_node_attr(func_ast).get('type') \
                    not in ['AST_FUNC_DECL', 'AST_CLOSURE', 'AST_METHOD',
                    'AST_TOPLEVEL']: # newly added
                G.add_blank_func_with_og_nodes(func_name, func_obj)
                func_ast = G.get_obj_def_ast_node(func_obj, aim_type='function')
            # add to coverage
            func_ast_attr = G.get_node_attr(func_ast)
            if 'labels:label' in func_ast_attr and \
                    func_ast_attr['labels:label'] == 'Artificial_AST':
                pass
            else:
                G.covered_func.add(func_ast)

            # add function scope (see comments in decl_function)
            parent_scope = G.get_node_attr(func_obj).get('parent_scope')
            new_scope_type = 'FUNC_SCOPE'
            if parent_scope == G.BASE_SCOPE:
                new_scope_type = 'FILE_SCOPE'
            func_scope = G.add_scope(new_scope_type, func_ast,
                f'Function{func_ast}:{call_ast}', func_obj,
                call_ast, func_name, parent_scope=parent_scope)
            # make arguments available in the function
            param_list = G.get_child_nodes(func_ast, edge_type='PARENT_OF',
                child_type='AST_PARAM_LIST')
            params = G.get_ordered_ast_child_nodes(param_list)
            # add "arguments" array
            arguments_obj = G.add_obj_to_scope(name='arguments',
                    js_type='array', scope=func_scope, ast_node=func_ast)
            j = 0
            while j < len(params) or j < len(_args) or j < 3:
                if j < len(_args):
                    arg_obj_nodes = to_obj_nodes(G, _args[j], call_ast)
                    # add argument to "arguments"
                    for obj in arg_obj_nodes:
                        G.add_obj_as_prop(prop_name=str(j),
                            parent_obj=arguments_obj, tobe_added_obj=obj)
                        if G.first_pass:
                            # add argument access path for function objs in args
                            # (saved call edges) -- initial access paths
                            arg_paths = G.get_node_attr(obj).get('arg_paths', set())
                            # G.set_node_attr(obj, ('arg_paths', arg_paths.union({f'{func_scope}:{j}'})))
                            arg_paths.add(f'{func_scope}:{j}')
                            G.set_node_attr(obj, ('arg_paths', arg_paths)) # for objs without arg_paths
                    # add argument to the parameter
                    if j < len(params):
                        param = params[j]
                        param_name = G.get_name_from_child(param)
                        if G.get_node_attr(param).get('flags:string[]') \
                            == 'PARAM_VARIADIC':
                            arr = G.add_obj_to_scope(param_name,
                                call_ast or param, 'array', scope=func_scope)
                            length = 0
                            while j < len(_args):
                                logger.debug(f'add arg {param_name}[{length}]'
                                    f' <- {arg_obj_nodes}, scope {func_scope}')
                                for obj in arg_obj_nodes:
                                    G.add_obj_as_prop(str(length),
                                        parent_obj=arr, tobe_added_obj=obj)
                                j += 1
                                length += 1
                            G.add_obj_as_prop('length', js_type='number',
                                value=length, parent_obj=arr)
                        else:
                            logger.debug(f'add arg {param_name} <- '
                                f'{arg_obj_nodes}, scope {func_scope}')
                            for obj in arg_obj_nodes:
                                G.add_obj_to_scope(name=param_name,
                                    scope=func_scope, tobe_added_obj=obj)
                    else:
                        # this is used to print logs only
                        logger.debug(f'add arg arguments[{j}] <- '
                            f'{arg_obj_nodes}, scope {func_scope}')
                elif j < len(params):
                    param = params[j]
                    param_name = G.get_name_from_child(param)
                    # print('param', param, G.get_ordered_ast_child_nodes(param), 'func', func_obj, func_ast)
                    # add dummy arguments
                    if G.get_node_attr(param).get('flags:string[]') \
                        == 'PARAM_VARIADIC':
                        # rest parameter (variable length arguments)
                        added_obj = G.add_obj_to_scope(name=param_name,
                            scope=func_scope, ast_node=call_ast or param,
                            js_type='array')
                        elem = G.add_obj_as_prop(wildcard, call_ast or param,
                            value=wildcard, parent_obj=added_obj)
                        if mark_fake_args:
                            G.set_node_attr(elem, ('tainted', True))
                            G.set_node_attr(elem, ('fake_arg', True))
                            # logger.debug("{} marked as tainted [2]".format(elem))
                    elif (G.get_node_attr(G.get_ordered_ast_child_nodes(param)
                            [2]).get('type') == 'NULL'): # without default value
                        added_obj = G.add_obj_to_scope(name=param_name,
                            scope=func_scope, ast_node=call_ast or param,
                            # give __proto__ when checking prototype pollution
                            js_type='object' if G.check_proto_pollution
                            else None, value=wildcard)
                    else:
                        child = G.get_ordered_ast_child_nodes(param)[2]
                        default_value = handle_node(G, child, extra)
                        added_obj = to_obj_nodes(G, default_value, child)[0]
                        G.add_obj_to_scope(name=param_name, scope=func_scope,
                            tobe_added_obj=added_obj)
                    if mark_fake_args:
                        G.set_node_attr(added_obj, ('tainted', True))
                        G.set_node_attr(added_obj, ('fake_arg', True))
                        # logger.debug("{} marked as tainted [3]".format(added_obj))
                    G.add_obj_as_prop(prop_name=str(j),
                        parent_obj=arguments_obj, tobe_added_obj=added_obj)
                    # add argument access path for function objs in args
                    # (saved call edges) -- initial access paths
                    if G.first_pass:
                        G.set_node_attr(added_obj, ('arg_paths', {f'{func_scope}:{j}'}))
                    logger.debug(f'add arg {param_name} <- new obj {added_obj}, '
                            f'scope {func_scope}, ast node {param}')
                elif j < 3:
                    # in case the function only use "arguments"
                    # but no parameters in its declaration
                    added_obj = G.add_obj_node(ast_node=call_ast,
                        # give __proto__ when checking prototype pollution
                        js_type='object' if G.check_proto_pollution
                        else None, value=wildcard)
                    if mark_fake_args:
                        G.set_node_attr(added_obj, ('tainted', True))
                        G.set_node_attr(added_obj, ('fake_arg', True))
                        # logger.debug("{} marked as tainted [4]".format(added_obj))
                    G.add_obj_as_prop(prop_name=str(j),
                        parent_obj=arguments_obj, tobe_added_obj=added_obj)
                    # add argument access path for function objs in args
                    # (saved call edges) -- initial access paths
                    if G.first_pass:
                        G.set_node_attr(added_obj, ('arg_paths', {f'{func_scope}:{j}'}))
                    logger.debug(f'add arguments[{j}] <- new obj {added_obj}, '
                                f'scope {func_scope}, ast node {call_ast}')
                else:
                    break
                j += 1
            arguments_length_obj = G.add_obj_as_prop(prop_name='length',
                    parent_obj=arguments_obj, value=j, js_type='number')

            # switch scopes ("new" will swtich scopes and object by itself)
            backup_scope = G.cur_scope
            G.cur_scope = func_scope
            G.scope_stack.append(G.cur_scope)
            backup_stmt = G.cur_stmt
            # # call the Python callback function
            # if python_callback is not None:
            #     python_callback(G)
            # run simulation -- create the object, or call the function
            if is_new:
                branch_created_obj, branch_returned_objs = instantiate_obj(G,
                    call_ast, func_ast, branches=next_branches)
                branch_created_objs = [branch_created_obj]
            else:
                backup_objs = G.cur_objs
                if _this:
                    G.cur_objs = _this.obj_nodes
                else:
                    G.cur_objs = [G.BASE_OBJ]
                branch_returned_objs, branch_used_objs = simurun_function(
                    G, func_ast, branches=next_branches, caller_ast=call_ast)
                
                G.cur_objs = backup_objs
            # switch back scopes
            G.cur_scope = backup_scope
            G.scope_stack.pop()
            G.cur_stmt = backup_stmt

            # delete "arguments" (avoid parent explosion)
            if not G.first_pass:
            # if True:
                for name_node in G.get_prop_name_nodes(arguments_obj):
                    for obj_node in G.get_child_nodes(name_node, edge_type='NAME_TO_OBJ'):
                        G.remove_all_edges_between(name_node, obj_node)
                    G.remove_all_edges_between(arguments_obj, name_node)

        # print('what the hell', func_ast, G.get_node_attr(func_ast).get('labels:label'), callback_functions)

        # if it's a dummy function
        if G.get_node_attr(func_ast).get('labels:label') \
            == 'Artificial_AST':
            # logger.info(sty.fg.green + sty.ef.inverse + func_ast + ' is a dummy function.' + sty.rs.all)
            if branch_used_objs is None: # in case it's skipped
                branch_used_objs = []
            if branch_returned_objs is None: # in case it's skipped
                branch_returned_objs = []
            # add arguments as used objects
            # arg_objs = [] -> branch_used_objs
            for h in _args:
                branch_used_objs.extend(to_obj_nodes(G, h, call_ast))
            if _this is not None:
                # performance is too low
                # for o in G.get_ancestors_in(func_obj, edge_types=[
                #     'NAME_TO_OBJ', 'OBJ_TO_PROP'],
                #     candidates=this.obj_nodes, step=2):
                #     branch_used_objs.append(o)
                branch_used_objs.extend(to_obj_nodes(G, _this, call_ast))
            body = G.get_child_nodes(func_ast, child_type='AST_STMT_LIST')[0]
            dummy_stmt = list(G.get_child_nodes(body, edge_type='PARENT_OF'))[0]
            # add a blank object as return object
            if not fake_returned_objs:
                added_obj = G.add_obj_node(
                    ast_node=dummy_stmt if G.new_trace_rule else call_ast,
                    js_type="object", value=wildcard)
                if G.get_node_attr(func_obj).get('tainted'):
                    G.set_node_attr(added_obj, ('tainted', True))
                fake_returned_objs.append(added_obj)
            # print('fake returned objs', fake_returned_objs)
            branch_returned_objs.extend(fake_returned_objs)
            for obj in branch_used_objs:
                add_contributes_to(G, [obj], fake_returned_objs[0])
            NodeHandleResult(ast_node=dummy_stmt, obj_nodes=fake_returned_objs,
                used_objs=branch_used_objs,
                callback=get_df_callback(G, ast_node=dummy_stmt if G.new_trace_rule else None))
            # add a blank object as created object
            if is_new and branch_created_objs == []:
                if not fake_created_objs:
                    added_obj = G.add_obj_node(
                        ast_node=dummy_stmt if G.new_trace_rule else call_ast, # really?
                        js_type="object", value=wildcard)
                    if G.get_node_attr(func_obj).get('tainted'):
                        G.set_node_attr(added_obj, ('tainted', True))
                    fake_created_objs.append(added_obj)
                branch_created_objs = fake_created_objs
                for obj in  branch_used_objs:
                    add_contributes_to(G, [obj], fake_created_objs[0])
                NodeHandleResult(ast_node=dummy_stmt, obj_nodes=fake_created_objs,
                    used_objs=branch_used_objs,
                    callback=get_df_callback(G, ast_node=dummy_stmt if G.new_trace_rule else None))

            # call all callback functions
            if callback_functions:
                logger.debug(sty.fg.green + sty.ef.inverse +
                    'callback functions = {}'.format(callback_functions)
                    + sty.rs.all)
                
                if _this is not None:
                    obj_attrs = [G.get_node_attr(obj) for obj in _this.obj_nodes]
                    mark_fake_args = any(['tainted' in attr for attr in obj_attrs])
                else:
                    mark_fake_args = False

                if len(callback_functions) != 0:
                    # if the name is OPGen_markTaintCall, mark the args as tainted
                    if "OPGen_markTaintCall" == func_name:
                        mark_fake_args = True

                call_function(G, callback_functions, call_ast=call_ast,
                    extra=extra, stmt_id=stmt_id, mark_fake_args=mark_fake_args)
                
        if G.first_pass:
            G.set_node_attr(func_ast, ('stored_created_objs', branch_created_objs))

        
        if branch_returned_objs is None or branch_used_objs is None: # workaround for skipping instantiating objects
            func_skipped = True
        # else:
        #     assert type(branch_returned_objs) is list
        #     assert type(branch_used_objs) is list
        #     returned_objs.update(branch_returned_objs)
        #     used_objs.update(branch_used_objs)
        # assert type(branch_created_obj) is not list
        # if branch_created_obj is not None:
        #     branch_created_objs.append(branch_created_obj)
    
    # print('what the ****?!', caller_ast, func_ast, G.get_node_attr(func_ast).get('type'))

    # No use at all!!
    # adding_cf = True
    # if type(func_name) is str and func_name.startswith("sink_hqbpillvul_"):
    #     if not _args:
    #         adding_cf = False
    #     else:
    #         has_tainted_obj = False
    #         for obj in _args[0].obj_nodes:
    #             if G.get_node_attr(obj).get('tainted'):
    #                 has_tainted_obj = True
    #         if not has_tainted_obj:
    #             adding_cf = False
                # print('skip adding cf for funtion', func_name, func_obj, func_ast, _args)

    # add control flows
    if call_ast is not None and func_ast is not None and \
            G.get_node_attr(func_ast).get('type') in [
                            'AST_FUNC_DECL', 'AST_CLOSURE', 'AST_METHOD']:
        caller_cpg = G.find_nearest_upper_CPG_node(call_ast)
        # logger.info(sty.fg.li_magenta + sty.ef.inverse + "CALLS" + 
        #     sty.rs.all + " {} -> {} (Line {} -> Line {}) {}".format(
        #         caller_cpg, func_ast,
        #         G.get_node_attr(caller_cpg).get('lineno:int'),
        #         G.get_node_attr(func_ast).get('lineno:int') or '?',
        #         func_name))
        # add a call edge from the expression to the function definition
        # G.add_edge_if_not_exist(
        #     caller_ast, func_ast, {"type:TYPE": "CALLS"})
        # add a call edge from the calling function to the callee
        # (called function)
        # print('caller ast', caller_ast, G.get_node_attr(caller_ast))
        caller_func = find_function(G, call_ast)
        if caller_func is not None:
            G.add_edge_if_not_exist(
                caller_func, func_ast, {"type:TYPE": "CALLS", "promise_related": promise_related})
            logger.info(sty.fg.li_magenta + sty.ef.inverse + "CALLS" + 
                sty.rs.all + " {} -> {} (Line {} -> Line {}) {} -> {}".format(
                    caller_func, func_ast,
                    G.get_node_attr(caller_func).get('lineno:int'),
                    G.get_node_attr(func_ast).get('lineno:int') or '?',
                    G.get_name_from_child(caller_func), func_name))
        else:
            logger.error('Cannot find the caller function for call {}->{}'
                .format(call_ast, func_ast))

        # then add a control flow edge from the statement to the
        # function's ENTRY node
        entry_node = G.get_successors(func_ast, edge_type='ENTRY')[0]
        G.add_edge_if_not_exist(
            caller_cpg, entry_node, {"type:TYPE": "FLOWS_TO"})
        # collect exit nodes
        exit_node = G.get_successors(func_ast, edge_type='EXIT')[0]
        exit_nodes.add(exit_node)
        logger.info(sty.fg.li_magenta + sty.ef.inverse + "FLOWS_TO" + 
            sty.rs.all + " {} -> {} (Line {} -> Line {}) {}".format(
                caller_cpg, entry_node,
                G.get_node_attr(caller_cpg).get('lineno:int'),
                G.get_node_attr(func_ast).get('lineno:int') or '?',
                func_name))

        # callback functions in arguments (function pointers)
        if G.first_pass:
            save_cf(G, func_obj, call_ast, branches, _args)

    G.call_stack.pop()
    # print(len(G.call_stack), G.call_stack)

    return branch_returned_objs, branch_created_objs, branch_used_objs, \
        func_run, func_skipped

def save_cf(G, func_obj, call_ast, branches, args=[]):
    tried = set()
    def _find_props(parent_obj, parent_obj_name):
        '''
        Find properties under an object.
        '''
        nonlocal G, tried
        proto_objs = \
            G.get_prop_obj_nodes(parent_obj=parent_obj, prop_name='__proto__')
        result_objs = []
        result_obj_names = []
        for name_node in G.get_prop_name_nodes(parent_obj):
            name = G.get_node_attr(name_node).get('name')
            if name in ['__proto__', 'prototype', 'constructor']: continue
            if name == wildcard: continue
            if name is None: continue
            obj_nodes = G.get_obj_nodes(name_node)
            for obj in obj_nodes:
                if obj in tried: continue
                result_objs.append(obj)
                result_obj_names.append(f'{parent_obj_name}.{name}')
        for proto_obj in proto_objs:
            for name_node in G.get_prop_name_nodes(proto_obj):
                name = G.get_node_attr(name_node).get('name')
                if name in ['__proto__', 'prototype', 'constructor']:
                    continue
                if name == wildcard: continue
                if name is None: continue
                obj_nodes = G.get_obj_nodes(name_node)
                for obj in obj_nodes:
                    if obj in tried: continue
                    result_objs.append((parent_obj, obj))
                    # result_obj_names.append(f'{cur_obj_name}.{name}')
                    result_obj_names.append(
                        f'{parent_obj_name}.__proto__.{name}')
        return result_objs, result_obj_names

    func_obj_origin_scope = None
    func_obj_origin_arg_num = None # deprecated
    func_obj_access_path = None
    _scope = G.cur_scope
    # while True:
    #     if G.get_node_attr(_scope).get('type') == 'FUNC_SCOPE':
    #         _arguments = G.get_objs_by_name(
    #             'arguments', scope=_scope, branches=branches)[0]
    #         # print('scope =', _scope, 'arguments =', _arguments)
    #         if _arguments:
    #             for _arg_name_node in G.get_prop_name_nodes(
    #                                     _arguments, exclude_proto=True):
    #                 _arg_objs = G.get_obj_nodes(_arg_name_node)
    #                 try:
    #                     arg_num = int(
    #                         G.get_node_attr(_arg_name_node).get('name'))
    #                 except (TypeError, ValueError):
    #                     continue
    #                 # print("arugment", G.get_node_attr(_arg_name_node).get('name'), _arg_objs)

    #                 # single step
    #                 # if func_obj in _arg_objs:
    #                 #     try:
    #                 #         func_obj_origin_arg_num = int(
    #                 #             G.get_node_attr(_arg_name_node).get('name'))
    #                 #         func_obj_origin_scope = _scope
    #                 #         break
    #                 #     except TypeError:
    #                 #         pass
                    
    #                 # multiple steps (can handle properties)
    #                 q = list(zip(_arg_objs, [str(arg_num)] * len(_arg_objs), [0] * len(_arg_objs)))
    #                 tried = set(_arg_objs)
    #                 depth_limit = 5
    #                 while q:
    #                     head_obj, head_name, head_depth = q.pop(0)
    #                     # print('trying...', f'#{arg_num}', 'in', _scope, head_obj, head_name, head_depth, func_obj)
    #                     if head_obj == func_obj:
    #                         func_obj_origin_scope = _scope
    #                         func_obj_origin_arg_num = arg_num
    #                         func_obj_access_path = head_name
    #                         break
    #                     elif head_depth < depth_limit:
    #                         _objs, _names = _find_props(head_obj, head_name)
    #                         q.extend(zip(_objs, _names, [head_depth + 1] * len(_objs)))
    #                         tried.update(_objs)
    #                 if func_obj_access_path is not None:
    #                     break
    #     if func_obj_access_path is not None:
    #         break
    #     edges = G.get_in_edges(_scope, edge_type='PARENT_SCOPE_OF')
    #     if edges:
    #         _scope = edges[0][0]
    #     else:
    #         break
    arg_paths = G.get_node_attr(func_obj).get('arg_paths')
    if not arg_paths: return
    while True:
        if G.get_node_attr(_scope).get('type') == 'FUNC_SCOPE':
            # print('scope =', _scope, 'candidates =', arg_paths)
            for arg_path in arg_paths:
                for seg in arg_path.split('.'):
                    match = re.match(r'(\d+):(\d+)', seg)
                    if match:
                        scope, arg = match[1], match[2]
                        if scope == _scope:
                            func_obj_origin_scope = scope
                            func_obj_access_path = arg_path
        if func_obj_access_path is not None:
            break
        edges = G.get_in_edges(_scope, edge_type='PARENT_SCOPE_OF')
        if edges:
            _scope = edges[0][0]
        else:
            break
    # print('fp?', func_obj, func_obj_origin_scope, G.cur_scope, func_obj_origin_arg_num, caller_func)
    if func_obj_origin_scope is not None:
        func_obj_origin_func = None
        try:
            func_obj_origin_func = G.get_out_edges(
                func_obj_origin_scope, edge_type='SCOPE_TO_AST')[0][1]
        except IndexError:
            logger.error('Error finding func ast for scope {}'.format(func_obj_origin_scope))
        # if caller_func is not None and func_obj_origin_arg_num is not None:
        if func_obj_origin_func is not None and func_obj_access_path is not None:
            saved_calls = \
                G.get_node_attr(func_obj_origin_func).get('saved_calls', [])
            duplicated = False
            for item in saved_calls:
                if item[0] == call_ast and item[1] == func_obj_access_path:
                    duplicated = True
            if not duplicated:
                saved_calls.append((call_ast, func_obj_access_path, args))
                G.set_node_attr(func_obj_origin_func, ('saved_calls', list(saved_calls)))
                logger.info(sty.fg.li_magenta + sty.ef.inverse +
                    "Call {} at arg {} saved to function {} {}".format(
                        call_ast, func_obj_access_path, func_obj_origin_func,
                        G.get_name_from_child(func_obj_origin_func)) + sty.rs.all)
                logger.info(sty.fg.li_magenta + 
                    "Arugments" + sty.rs.all + " {}".format(args) )

def add_saved_cf(G, func_ast, call_ast, args, branches):
    # Generally:
    # function that contains call_ast (F0)
    #     ↓  calls
    # func_ast (F1)
    #     ↓  calls
    # functions in args (F2)
    #     ↓  calls
    # functions in saved_args (F3)
    #     ⋮  (recursively)
    #
    # Specifically:
    # (1) We don't need to create edges for F0 and F1 because they has
    # been created in normal ways, and it's not related to saved CF.
    # (2) func_ast is a function definition AST node (F1). We find the
    # call expressions that call F2 from its saved_calls attribute.
    # (3) saved_calls memorize the AST node numbers of the call
    # expressions, access path (how to find F2 from args) and the
    # arguments to call F2 with, because F2 may be called with objects
    # that contain other callback functions (F3). We call add_saved_cf
    # recursively to create edges for F2 and F3.
    def find_prop_by_path(cur_obj, path, arg_seg, arg_obj):
        nonlocal G, branches
        if not path:
            return [cur_obj]
        name = None
        if arg_seg == 0:
            if cur_obj is None:
                return find_prop_by_path(arg_obj, path[1:], arg_seg - 1, None)
            else:
                value = G.get_node_attr(arg_obj).get('code')
                if value == wildcard or value == undefined:
                    return []
                else:
                    name = val_to_str(value)
        else:
            name = path[0]
        if cur_obj is None:
            next_objs = G.get_objs_by_name(name, branches=branches)
        else:
            next_objs = G.get_prop_obj_nodes(
                cur_obj, prop_name=name, branches=branches)
        if len(path) == 1:
            return next_objs
        else:
            l = []
            for obj in next_objs:
                l.extend(find_prop_by_path(obj, path[1:], arg_seg - 1, arg_obj))
            return l
    # def find_prop_by_path(cur_obj, rest_path):
    #     nonlocal branches
    #     if not rest_path:
    #         return [cur_obj]
    #     next_objs = G.get_prop_obj_nodes(
    #         cur_obj, prop_name=rest_path[0], branches=branches)
    #     if len(rest_path) == 1:
    #         return next_objs
    #     else:
    #         l = []
    #         for obj in next_objs:
    #             l.extend(find_prop_by_path(obj, rest_path[1:]))
    #         return l
    def add_additional_paths(arg_obj, split_original_path, seg_in_original_path,
            call_ast, saved_args):
        nonlocal G, func_ast
        arg_paths = G.get_node_attr(arg_obj).get('arg_paths')
        if not arg_paths:
            return
        for path in arg_paths:
            scope = None
            split_new_path = list(split_original_path)
            for i, seg in enumerate(path.split('.')):
                match = re.match(r'(\d+):(\d+)', seg)
                if match:
                    scope = match[1]
                    seg_num = i
                    break
            if scope is None:
                continue
            origin_func_ast = G.get_out_edges(scope, edge_type='SCOPE_TO_AST')[0][1]
            if func_ast == origin_func_ast:
                # logger.error("Error: ", 
                #     f"trying to replace paths in the same function {func_ast}")
                pass
            saved_calls = G.get_node_attr(origin_func_ast).get('saved_calls', [])
            old_path_seg = split_new_path[seg_in_original_path]
            if path in old_path_seg or old_path_seg in path:
                logger.error("Error: recursive path replace attempt: "
                    r"replacing {} with {}".format(old_path_seg, path) + sty.rs.all)
                continue
            split_new_path[seg_in_original_path] = path
            new_path = '.'.join(split_new_path)
            duplicated = False
            for item in saved_calls:
                if item[0] == call_ast and item[1] == new_path:
                    duplicated = True
            if duplicated:
                continue
            saved_calls.append((call_ast, new_path, args))
            G.set_node_attr(origin_func_ast, ('saved_calls', saved_calls))
            logger.info(sty.fg.li_magenta + sty.ef.inverse +
                "Call {} at alt arg {} saved to function {} {}".format(
                    call_ast, new_path, origin_func_ast,
                    G.get_name_from_child(origin_func_ast)) + sty.rs.all)
            logger.info(sty.fg.li_magenta + 
                "by replacing {} with {}".format(old_path_seg, path) + sty.rs.all)
            logger.info(sty.fg.li_magenta + 
                "Arugments" + sty.rs.all + " {}".format(saved_args) )
    # saved 
    saved_calls = G.get_node_attr(func_ast).get('saved_calls', [])
    logger.debug('Saved calls in function {} are {}'.format(func_ast, saved_calls))
    logger.debug('Function {} is called with args {}'.format(func_ast, args))
    for saved_call in saved_calls:
        if saved_call is not None:
            saved_call_ast, saved_access_path, saved_args = saved_call
            saved_call_cpg = G.find_nearest_upper_CPG_node(saved_call_ast)
            saved_caller = find_function(G, saved_call_ast)
            split_path = saved_access_path.split('.')
            saved_arg_num = None
            seg_num = None
            try:
                # saved_arg_num = int(saved_access_path.split('.', 1)[0])
                for i, seg in enumerate(split_path):
                    match = re.match(r'(\d+):(\d+)', seg)
                    if match:
                        saved_arg_num = int(match[2])
                        seg_num = i
                        break
            except (TypeError, ValueError, IndexError):
                logger.error('Saved call ' + str(saved_call) + 'error!')
            if saved_arg_num is not None and saved_arg_num < len(args):
                for arg_obj in to_obj_nodes(G, args[saved_arg_num], call_ast):
                    # if there are any alternative paths
                    if len(split_path) < 6:
                        add_additional_paths(arg_obj, split_path,
                            seg_num, saved_call_ast, saved_args)
                    # handle solvable paths
                    callee_objs = find_prop_by_path(None, split_path, seg_num, arg_obj)
                    logger.debug('Found callee objs from arg {} by path #{}: {}'.format(arg_obj, saved_access_path, callee_objs))
                    for callee_obj in callee_objs:
                        callee_ast = G.get_obj_def_ast_node(callee_obj, aim_type='function')
                        if callee_ast is None: continue
                        callee_name = G.get_node_attr(callee_obj).get('name') or '?'
                        if G.get_node_attr(callee_ast).get('type') in [
                                'AST_FUNC_DECL', 'AST_CLOSURE', 'AST_METHOD']:
                            G.add_edge_if_not_exist(
                                saved_caller, callee_ast, {"type:TYPE": "CALLS"})
                            callee_entry_node = \
                                G.get_successors(callee_ast, edge_type='ENTRY')[0]
                            G.add_edge_if_not_exist(
                                saved_call_cpg, callee_entry_node, {"type:TYPE": "FLOWS_TO"})
                            callee_exit_node = \
                                G.get_successors(callee_ast, edge_type='EXIT')[0]
                            G.add_edge_if_not_exist(
                                callee_exit_node, saved_call_cpg, {"type:TYPE": "FLOWS_TO"})
                            logger.info(sty.fg.li_magenta + sty.ef.inverse + "Saved CALLS" + 
                                sty.rs.all + " {} -> {} (Line {} -> Line {}) {} -> {} at arg {}".format(
                                    saved_caller, callee_ast,
                                    G.get_node_attr(saved_caller).get('lineno:int'),
                                    G.get_node_attr(callee_ast).get('lineno:int') or '?',
                                    G.get_name_from_child(saved_caller), callee_name,
                                    saved_access_path))
                            logger.info(sty.fg.li_magenta + sty.ef.inverse + "Saved FLOWS_TO ENTRY" + 
                                sty.rs.all + " {} -> {} (Line {} -> Line {}) {}".format(
                                    saved_call_cpg, callee_entry_node,
                                    G.get_node_attr(saved_call_cpg).get('lineno:int'),
                                    G.get_node_attr(callee_ast).get('lineno:int') or '?',
                                    callee_name))
                            logger.info(sty.fg.li_magenta + sty.ef.inverse + "Saved FLOWS_TO EXIT" + 
                                sty.rs.all + " {} -> {} (Line {} -> Line {}) {}".format(
                                    callee_exit_node, saved_call_cpg,
                                    G.get_node_attr(callee_ast).get('lineno:int'),
                                    G.get_node_attr(saved_call_cpg).get('lineno:int') or '?',
                                    callee_name))
                        # continue propagating upwards
                        # TODO: ?
                        # save_cf(G, callee_obj, call_ast, branches)
                        # continue propagating downwards
                        # for arg in saved_args:
                        #     for arg_obj in arg.obj_nodes:
                        #         if G.get_node_attr(obj).get('type') == 'function':
                        #             arg_ast = G.get_obj_def_ast_node(arg_obj, aim_type='function')
                        #             if arg_ast is None: continue
                        #                 saved_call = G.get_node_attr(func_ast).get('saved_call')
                        add_saved_cf(G, callee_ast, func_ast, saved_args, branches)


def merge(G, stmt, num_of_branches, parent_branch):
    '''
    Merge two or more branches.
    
    Args:
        G: graph
        stmt: AST node ID of the if/switch statement.
        num_of_branches (int): number of branches.
        parent_branch (BranchTag): parent branch tag (if this branch is
            inside another branch statement).
     '''
    start_time = time.time()
    logger.debug(f'Merging branches in {stmt}')
    # name_nodes = G.get_node_by_attr('labels:label', 'Name')
    # name_nodes = G.name_nodes
    name_nodes = G.affected_name_nodes[-1]
    for u in name_nodes:
        for v in G.get_child_nodes(u, 'NAME_TO_OBJ'):
            created = [False] * num_of_branches
            deleted = [False] * num_of_branches
            for key, edge_attr in G.graph[u][v].items():
                branch_tag = edge_attr.get('branch')
                if branch_tag and branch_tag.point == stmt:
                    if branch_tag.mark == 'A':
                        created[int(branch_tag.branch)] = True
                    if branch_tag.mark == 'D':
                        deleted[int(branch_tag.branch)] = True
            # logger.debug(f'{u}->{v}\ncreated: {created}\ndeleted: {deleted}')

            # We flatten Addition edges if they exist in any branch, because
            # the possibilities will continue to exist in parent branches.
            # We ignore those edges without tags related to current
            # statement.
            flag_created = any(created)
            # We always delete Deletion edges because they are useless in
            # parent branches.
            # If they exist in all current branches, the Addition edge in the
            # parent branch will be deleted (or maked by a Deletion edge).
            flag_deleted = deleted and all(deleted)

            # if flag_created or flag_deleted:
            #     logger.debug(f'{u}->{v}\ncreated: {created}\ndeleted: {deleted}')

            # we'll delete edges, so we save them in a list
            # otherwise the graph is changed and Python will raise an error
            edges = list(G.graph[u][v].items())

            # deleted all branch edges (both Addition and Deletion)
            for key, edge_attr in edges:
                branch_tag = edge_attr.get('branch', BranchTag())
                if branch_tag.point == stmt:
                    G.graph.remove_edge(u, v, key)

            # flatten Addition edges
            if flag_created:
                # logger.debug(f'add edge {u}->{v}, branch={stmt}')
                if parent_branch:
                    # add one addition edge with parent if/switch's (upper level's) tags
                    # logger.debug(f"create edge {u}->{v}, branch={BranchTag(parent_branch, mark='A')}")
                    G.add_edge(u, v, {'type:TYPE': 'NAME_TO_OBJ', 'branch': BranchTag(parent_branch, mark='A')})
                else:
                    # logger.debug(f'create edge {u}->{v}')
                    G.add_edge(u, v, {'type:TYPE': 'NAME_TO_OBJ'})

            # cancel out Deletion edges
            if flag_deleted:
                if parent_branch:
                    # find if there is any addition in parent if/switch (upper level)
                    flag = False
                    for key, edge_attr in list(G.graph[u][v].items()):
                        branch_tag = edge_attr.get('branch', BranchTag())
                        if branch_tag == BranchTag(parent_branch, mark='A'):
                            # logger.debug(f'delete edge {u}->{v}')
                            G.graph.remove_edge(u, v, key)
                            flag = True
                    # if there is not
                    if not flag:
                        # add one deletion edge with parent if/switch's (upper level's) tags
                        # logger.debug(f"create edge {u}->{v}, branch={BranchTag(parent_branch, mark='D')}")
                        G.add_edge(u, v, {'type:TYPE': 'NAME_TO_OBJ', 'branch': BranchTag(parent_branch, mark='D')})
                else:
                    # find if there is an addition in upper level
                    for key, edge_attr in list(G.graph[u][v].items()):
                        if 'branch' not in edge_attr:
                            # logger.debug(f'delete edge {u}->{v}')
                            G.graph.remove_edge(u, v, key)
    G.timing('>merge', time.time() - start_time)

def decl_function(G, node_id, func_name=None, obj_parent_scope=None,
    scope_parent_scope=None, add_to_scope=True):
    '''
    Declare a function as an object node.
    
    Args:
        G (Graph): Graph.
        node_id: The function's AST node (AST_FUNC_DECL).
        func_name (str, optional): The function's name. Defaults to
            None, which means getting name from its AST children.
        obj_parent_scope (optional): Which scope the function object
            should be placed to. Defaults to current scope.
        scope_parent_scope (optional): Where the function's scopes
            should be put. See comments below. Defaults to current
            scope.
    
    Returns:
        added_obj: The function's object node.
    '''
    # for a function decl, if already visited, return
    # if "VISITED" in G.get_node_attr(node_id):
    #     return None

    if obj_parent_scope is None:
        # obj_parent_scope = G.cur_scope
        obj_parent_scope = G.find_ancestor_scope()
    if scope_parent_scope is None:
        scope_parent_scope = G.cur_scope
    if func_name is None:
        func_name = G.get_name_from_child(node_id)

    # add function declaration object
    added_obj = G.add_obj_node(node_id, "function")
    G.set_node_attr(added_obj, ('name', func_name))
    # memorize its parent scope
    # Function scopes are not created when the function is declared.
    # Instead, they are created before each time the function is
    # executed. Because the function can be called in any scope but its
    # scope should be put under where it is defined, we need to memorize
    # its original parent scope.
    G.set_node_attr(added_obj, ('parent_scope', scope_parent_scope))
    G.set_node_attr(added_obj, ('parent_scope_this', G.cur_objs))

    if func_name is not None and func_name != '{anon}' and add_to_scope:
        G.add_obj_to_scope(name=func_name, scope=obj_parent_scope,
            tobe_added_obj=added_obj)
        name_node = G.get_name_node(func_name, scope=obj_parent_scope,
            follow_scope_chain=False)
        G.set_node_attr(name_node, ('statically_declared', True))
        # input('static')
        G.add_obj_as_prop('name', node_id, 'string', func_name, added_obj)

    param_list = G.get_child_nodes(node_id, edge_type='PARENT_OF',
        child_type='AST_PARAM_LIST')[0]
    params = G.get_ordered_ast_child_nodes(param_list)
    length = len(params)
    if length > 0:
        if G.get_node_attr(params[-1]).get('flags:string[]') \
            == 'PARAM_VARIADIC':
            length -= 1
    G.add_obj_as_prop('length', node_id, 'number', length, added_obj)

    # G.set_node_attr(node_id, ("VISITED", "1"))
    logger.debug(f'{sty.ef.b}Declare function{sty.rs.all} {func_name} {node_id}'
        f' as {added_obj} in {obj_parent_scope}')

    if G.first_pass and scope_parent_scope != G.BASE_SCOPE: # not a file
    # if G.first_pass:
        cur_file_path = G.file_stack[-1] if G.file_stack else None
        G.stack2.append((added_obj, func_name, None, [], None, cur_file_path))

    return added_obj

def run_toplevel_file(G: Graph, node_id):
    """
    run a top level file 
    return a obj and scope
    """
    # switch current file path
    if 'name' in G.get_node_attr(node_id):
        file_path = G.get_node_attr(node_id)['name']
    else:
        print(node_id, G.get_node_attr(node_id))
        return None

    # loop call
    if file_path in G.file_stack:
        logger.info(sty.ef.b + '{} in the file stack, skipped.'.format(file_path) + sty.rs.all)
        return None
    G.file_stack.append(file_path)
    print(G.file_stack)
    previous_file_path = G.cur_file_path
    G.cur_file_path = file_path
    if G.entry_file_path is None:
        G.entry_file_path = file_path
    logger.info(sty.fg(173) + sty.ef.inverse + 'FILE {} BEGINS'.format(file_path) + sty.rs.all)

    # add function object and scope
    func_decl_obj = decl_function(G, node_id, func_name=file_path,
        obj_parent_scope=G.BASE_SCOPE, scope_parent_scope=G.BASE_SCOPE)
    func_scope = G.add_scope(scope_type='FILE_SCOPE', decl_ast=node_id,
        scope_name=G.scope_counter.gets(f'File{node_id}'),
        decl_obj=func_decl_obj, func_name=file_path, parent_scope=G.BASE_SCOPE)

    backup_scope = G.cur_scope
    G.cur_scope = func_scope
    G.scope_stack.append(G.cur_scope)
    backup_stmt = G.cur_stmt

    # add module object to the current file's scope
    added_module_obj = G.add_obj_to_scope("module", node_id)
    # add module.exports
    added_module_exports = G.add_obj_as_prop("exports", node_id,
        parent_obj=added_module_obj)
    # add module.exports as exports
    G.add_obj_to_scope(name="exports", tobe_added_obj=added_module_exports)
    # "this" is set to module.exports by default
    # backup_objs = G.cur_objs
    # G.cur_objs = added_module_exports
    # TODO: this is risky
    G.add_obj_to_scope(name="this", tobe_added_obj=added_module_exports)
    prev_dont_quit = G.dont_quit
    G.dont_quit = 'file'

    # simurun the file
    simurun_function(G, node_id, block_scope=True)

    G.dont_quit = prev_dont_quit

    if G.first_pass:
        empty_rough_stacks(G, reason='run_toplevel_file')

    # get current module.exports
    # because module.exports may be assigned to another object
    # TODO: test if module is assignable
    # module_obj = G.get_objs_by_name('module')[0]
    module_obj = added_module_obj
    module_exports_objs = G.get_prop_obj_nodes(parent_obj=module_obj,
        prop_name='exports')

    # switch back scope, object, path and statement AST node id
    G.cur_scope = backup_scope
    G.scope_stack.pop()
    # G.cur_objs = backup_objs
    G.last_stmts = [G.cur_stmt]
    G.cur_stmt = backup_stmt

    # always rerun the file
    if G.two_pass and G.first_pass:
        # print('start to rerun the file', file_path)
        G.stack1.append((func_decl_obj, file_path, None, [], None, file_path))
        empty_rough_stacks(G, 'file_finished')
        # print('end', file_path)

    if not (G.two_pass and not G.first_pass):
        cf_search_complete(G, node_id, f'main', file_path=file_path)

    G.cur_file_path = previous_file_path
    G.file_stack.pop(-1)

    return module_exports_objs

def cf_search_complete(G, source_ast, source_name='?', root=None, file_path=None):
    logger.debug(sty.fg.li_magenta +
        f'Start CF search from {source_ast} {source_name}' + sty.rs.all)
    if G.first_pass:
        # shouldn't change if it's running entries in G.cf_searches
        G.cf_searches.add((source_ast, source_name, root, file_path))
    rel_file_path = None
    if file_path:
        rel_file_path = os.path.relpath(file_path, G.entry_file_path)
    output = {
        "source": {"node": source_ast, "name": source_name},
        "entry_file": G.entry_file_path,
        "cur_file": G.get_node_file_path(source_ast)
    }
    def print_func(x):
        if x.endswith('REACHABLE'):
            return x
        node_type = G.get_node_attr(x).get('type')
        if node_type in ['AST_FUNC_DECL', 'AST_CLOSURE', 'AST_METHOD']:
            func_name = G.get_name_from_child(x)
            if type(func_name) is not str or func_name.startswith('{anon'):
                alias = G.get_node_attr(x).get('alias')
                if alias:
                    func_name = alias
            return (sty.fg.cyan + x + ' ' + sty.rs.all + 
                str(func_name))
        elif node_type == 'CFG_FUNC_ENTRY':
            func_ast = G.get_in_edges(x, edge_type='ENTRY')[0][0]
            return (sty.fg.cyan + x + ' ' + sty.rs.all + 
                str(G.get_name_from_child(func_ast)))
        elif node_type == 'CFG_FUNC_EXIT':
            func_ast = G.get_in_edges(x, edge_type='EXIT')[0][0]
            return (sty.fg.cyan + x + ' ' + sty.rs.all +
                str(G.get_name_from_child(func_ast)) + ' EXIT')
        elif node_type == 'AST_TOPLEVEL':
            return (sty.fg.cyan + x + sty.rs.all + ' File')
        else:
            return (sty.fg.cyan + x + ' ' + sty.rs.all + 'L' +
                str(G.get_node_attr(x).get('lineno:int') or '?'))
    def serialize_func(x):
        if x.endswith('REACHABLE'):
            return {"type": x}
        node_type = G.get_node_attr(x).get('type')
        lineno = G.get_node_attr(x).get('lineno:int')
        name = G.get_name_from_child(x)
        if node_type == 'CFG_FUNC_ENTRY':
            func_ast = G.get_in_edges(x, edge_type='ENTRY')[0][0]
            name = G.get_name_from_child(func_ast)
        elif node_type == 'CFG_FUNC_EXIT':
            func_ast = G.get_in_edges(x, edge_type='EXIT')[0][0]
            name = G.get_name_from_child(func_ast)
        return {
            "id": int(x),
            "type": node_type,
            "name": name,
            "lineno": int(lineno) if lineno is not None and lineno != '' else None
        }

    source_entry = G.get_successors(source_ast, edge_type='ENTRY')[0]
    # CG search
    cg_paths = list(cg_dfs(G, source_ast, [source_ast]))
    output['call_paths'] = []
    if not cg_paths:
        logger.debug(sty.fg.li_grey + 'Nothing found.' + sty.rs.all)
    else:
        logger.info(sty.fg.li_magenta + sty.ef.b +
            f'Call graph paths from {source_ast} {source_name} '
            f'({rel_file_path}):' + sty.rs.all)
    for path in cg_paths:
        logger.info('->'.join(map(print_func, path)))
        output['call_paths'].append(list(map(serialize_func, path)))
        G.cg_paths.append(list(path))
        G.allowed_exported_funcs.update(path)
    cg_nodes = set(chain(*cg_paths))
    # if cg_paths: input()
    if not cg_nodes: return False
    if cg_paths and G.exit_when_found:
        cg_paths = [cg_paths[0]]

    # CF search
    # logger.info(sty.fg.li_magenta + sty.ef.b +
    #     f'Possible paths from {cur_obj_name}:' + sty.rs.all)
    # nop = defaultdict(int)
    # any_path = False
    # for path in cf_dfs(G, cur_entry_node, [cur_entry_node],
    #                    nop=nop, cg_nodes=cg_nodes):
    #                 #  nop=nop, cg_nodes=None): # disable CG nodes
    #     any_path = True
    #     logger.info('->'.join(map(print_func, path)))
    #     if path[-1] == 'REACHABLE':
    #         path = path[:-1]
    #     # add control flows from current function to the sink
    #     G.possible_cf_nodes.update(path)
    #     if G.exit_when_found:
    #         break
    # if bool(cg_nodes) != bool(any_path): input('*** Error')
    # if not any_path: continue

    # pair-based intra-function CF search
    nop = defaultdict(int)
    any_path = False
    output['cf_paths'] = []
    for path in cg_paths:
        if path[-1] == 'REACHABLE':
            path = path[:-1]
        logger.info('Intra-procedural:')
        for i in range(1, len(path)):
            source, sink = map(
                lambda n: G.get_successors(n, edge_type='ENTRY')[0],
                [path[-i-1], path[-i]]
            )
            paths_serialized = []
            output['cf_paths'].append({
                'from': path[-i-1],
                'to': path[-i],
                'paths': paths_serialized
            })
            path_debug = []
            G.cf_paths.append((path[-i-1], path[-i], path_debug))
            dfs = cf_dfs_inside(G, source, [source], target=sink, nop=nop)
            for cf_path in dfs:
                any_path = True
                logger.info('  ' + sty.fg.li_magenta +
                    f'{path[-i-1]}->{path[-i]}' + sty.rs.all +
                    ': ' + '->'.join(map(print_func, cf_path)))
                paths_serialized.append(list(map(serialize_func, cf_path)))
                path_debug.append(list(cf_path))
                if cf_path[-1] == 'REACHABLE':
                    cf_path = cf_path[:-1]
                G.possible_cf_nodes.update(cf_path)
                if G.exit_when_found:
                    break
    # if bool(cg_nodes) != bool(any_path): input('*** Error')
    if not any_path: return False

    # if G.exit_when_found:
    #     G.finished = True # stop first pass when any CF path is found
    # # avoid using it in the first pass!!
    if G.first_pass:
        # G.vul_files.add(G.file_stack[-1]) # why?
        G.vul_files.add(file_path)
    
    # output number of CF paths
    nop_print = []
    for n in nop:
        t = G.get_node_attr(n).get('type')
        if t in ['AST_IF', 'AST_IF_ELEM', 'AST_CALL', 'AST_SWITCH',
                'AST_SWITCH_CASE', 'AST_FOR', 'AST_WHILE']:
            nop_print.append((n, '  ' + sty.fg.li_cyan + n + 
                sty.rs.all + ' ' + t + ' Line ' +
                str(G.get_node_attr(n).get('lineno:int'))
                + ': ' + str(nop[n])))
    nop_print.sort()
    nop_print = list(map(lambda x: x[1], nop_print))
    logger.debug('Branch selection:')
    logger.debug('\n'.join(nop_print))
    nop = nop[source_entry]
    logger.info(f'Number of CF Paths: {nop}')
    G.num_of_cf_paths += nop

    # search for preceding CF paths
    output['prec_call_paths'] = []
    output['prec_cf_paths'] = []
    if root is not None:
        # may time out
        # root_entry = G.get_successors(root, edge_type='ENTRY')[0]
        # # add control flows from root to current function
        # logger.info(sty.fg.li_magenta + sty.ef.b +
        #     f'Possible preceding paths:' + sty.rs.all)
        # prec_nop = defaultdict(int)
        # paths2 = list(cf_dfs(G, root_entry, [root_entry],
        #     targets=[source_entry], nop=prec_nop)) # may cause timeout
        # for path in paths2:
        #     logger.info('->'.join(map(print_func, path)))
        #     if path[-1] == 'REACHABLE':
        #         path = path[:-1]
        #     G.possible_cf_nodes.update(path)
        #     if G.exit_when_found:
        #         break
        # prec_nop = prec_nop[root_entry]
        # logger.info(f'Number of Preceding CF Paths: {prec_nop}')
        # G.num_of_prec_cf_paths += prec_nop
        # G.num_of_full_cf_paths += nop * prec_nop

        # call graph search first
        root_entry = G.get_successors(root, edge_type='ENTRY')[0]
        logger.info(sty.fg.li_magenta + sty.ef.b +
            f'Possible preceding call graph paths to {source_name} '
            f'(root {root}->{source_ast}):' + sty.rs.all)
        # prec_cg_paths = list(cg_dfs(G, root, [root], targets=[source_ast]))
        prec_cg_paths = list(cg_dfs(G, root, [root], targets=[source_ast], edge_type='RUNS_BEFORE'))
        for path in prec_cg_paths:
            logger.info('->'.join(map(print_func, path)))
            output['prec_call_paths'].append(list(map(serialize_func, path)))
            G.allowed_exported_funcs.update(path)
        prec_cg_nodes = set(chain(*prec_cg_paths))
        prec_nop = defaultdict(int)
        if prec_cg_nodes:
            if prec_cg_paths and G.exit_when_found:
                prec_cg_paths = [prec_cg_paths[0]]
            # then CFG search
            for path in prec_cg_paths:
                paths_serialized = []
                if path[-1] == 'REACHABLE':
                    path = path[:-1]
                for i in range(1, len(path)):
                    source, sink = map(
                        lambda n: G.get_successors(n, edge_type='ENTRY')[0],
                        [path[-i-1], path[-i]]
                    )
                    output['prec_cf_paths'].append({
                        'from': path[-i-1],
                        'to': path[-i],
                        'paths': paths_serialized
                    })
                    # dfs = cf_dfs_inside(G, source, [source], target=sink, nop=prec_nop)
                    dfs = cf_dfs_inside(G, source, [source], target=None, nop=prec_nop)
                    for cf_path in dfs:
                        any_path = True
                        logger.info(sty.fg.li_magenta + sty.ef.b +
                            f'{path[-i-1]}->{path[-i]}' + sty.rs.all +
                            ': ' + '->'.join(map(print_func, cf_path)))
                        paths_serialized.append(list(map(serialize_func, cf_path)))
                        if cf_path[-1] == 'REACHABLE':
                            cf_path = cf_path[:-1]
                        G.possible_cf_nodes.update(cf_path)
                if G.exit_when_found:
                    break
        prec_nop = prec_nop[root_entry]
        logger.info(f'Number of Preceding CF Paths: {prec_nop}')
        G.num_of_prec_cf_paths += prec_nop
        G.num_of_full_cf_paths += nop * prec_nop
    else:
        G.num_of_full_cf_paths += nop

    with open('./cf_paths.ndjson', 'a') as fp:
        fp.write(json.dumps(output) + '\n')

    return True

def handle_require_legacy(G, node_id, extra=None):
    '''
    Returns:
        List: returned module.exports objects. we need to list the exported functions recursively
    '''
    # handle module name
    arg_list = G.get_ordered_ast_child_nodes(
        G.get_ordered_ast_child_nodes(node_id)[-1] )
    handled_module_name = handle_node(G, arg_list[0], extra)
    module_names = to_values(G, handled_module_name, node_id)[0]
    if not module_names: return []

    returned_objs = set()
    for module_name in module_names:
        if module_name in modeled_builtin_modules.modeled_modules \
            and G.vul_type != "path_traversal":
            # Python-modeled built-in modules
            # for now mostly fs
            # if it's path_traversal, do not do this
            returned_objs.add(
                modeled_builtin_modules.get_module(G, module_name))
        else:
            # actual JS modules
            # static require (module name is a literal)
            # module's path is in 'name' field
            file_path = G.get_node_attr(node_id).get('name')
            module_exports_objs = []
            if module_name and file_path:
                module_exports_objs = \
                    get_module_exports(G, file_path)
            # dynamic require (module name is a variable)
            if module_name is None or module_name == wildcard:
                logger.error('{} trying to require unknown package.'
                    .format(node_id))
                continue
            if not module_exports_objs:
                # check if the file's AST is in the graph
                file_path, _ = \
                    esprima_search(module_name, G.get_cur_file_path(),
                        print_func=logger.info)
                if not file_path: # module not found
                    continue
                elif file_path == 'built-in': # unmodeled built-in module
                    continue
                else:
                    module_exports_objs = \
                        get_module_exports(G, file_path)
            if not module_exports_objs:
                # if the file's AST is not in the graph,
                # generate its AST and run it
                logger.log(ATTENTION, f'Generating AST on demand for module '
                    f'{module_name} at {file_path}...')

                # following code is copied from analyze_files,
                # consider combining in future.
                start_id = str(G.cur_id)
                result = esprima_parse(file_path, ['-n', start_id, '-o', '-'],
                    print_func=logger.info)
                G.import_from_string(result)
                # start from the AST_TOPLEVEL node instead of the File node
                module_exports_objs = \
                        run_toplevel_file(G, str(int(start_id) + 1))
                G.set_node_attr(start_id,
                    ('module_exports', module_exports_objs))
            if module_exports_objs:
                returned_objs.update(module_exports_objs)
            else:
                logger.error("Required module {} at {} not found!".format(
                    module_name, file_path))
    return list(returned_objs)

def handle_require(G: Graph, caller_ast, extra, _, module_names):
    # handle module name
    module_names, src, _ = to_values(G, module_names, caller_ast)
    if not module_names: return NodeHandleResult(obj_nodes=[])
    built_in_vul_list = ['path_traversal', 'file_write', 'xss']

    returned_objs = set()
    for module_name in module_names:
        if module_name in modeled_builtin_modules.modeled_modules \
            and G.vul_type not in built_in_vul_list:
            # Python-modeled built-in modules
            # for now mostly fs
            # if it's path_traversal, do not do this
            returned_objs.add(
                modeled_builtin_modules.get_module(G, module_name))
        else:
            # actual JS modules
            # static require (module name is a literal)
            # module's path is in 'name' field
            file_path = G.get_node_attr(caller_ast).get('name')
            module_exports_objs = []
            file_ast_node = None
            if module_name and file_path:
                module_exports_objs, file_ast_node = \
                    get_module_exports(G, file_path)
            # dynamic require (module name is a variable)
            if module_name is None or module_name == wildcard:
                logger.error('{} trying to require an unknown package.'
                    .format(caller_ast))
                continue
            if module_name.endswith('package.json'):
                module_name = module_name.rstrip('package.json')
            if not module_exports_objs:
                # check if the file's AST is in the graph
                require_from = G.get_cur_file_path()
                if require_from == os.path.normpath(os.path.abspath(__file__)
                                        + '../../../builtin_packages/pm.js'):
                    require_from = G.file_stack[-2]
                file_path, _ = esprima_search(module_name, require_from,
                                              print_func=logger.info)
                if not file_path: # module not found
                    continue
                elif file_path == 'built-in': # unmodeled built-in module
                    continue
                else:
                    module_exports_objs, file_ast_node = \
                        get_module_exports(G, file_path)
            if not module_exports_objs and not file_ast_node:
                # if the file's AST is not in the graph,
                # generate its AST and run it
                logger.log(ATTENTION, f'Generating AST on demand for module '
                    f'{module_name} at {file_path}...')

                # following code is copied from analyze_files,
                # consider combining in future.
                start_id = str(G.cur_id)
                result = esprima_parse(file_path, ['-n', start_id, '-o', '-'],
                    print_func=logger.info)
                G.import_from_string(result)
                # start from the AST_TOPLEVEL node instead of the File node
                # children = G.get_child_nodes(start_id, 'PARENT_OF') # why? shouldn't it be FILE_OF?
                children = G.get_child_nodes(start_id)
                if children:
                    file_ast_node = children[0]
                    module_exports_objs = \
                            run_toplevel_file(G, file_ast_node)
                    G.set_node_attr(start_id,
                        ('module_exports', module_exports_objs))
                else:
                    logger.error(f'File {start_id} has no children')
            if module_exports_objs:
                returned_objs.update(module_exports_objs)
                builtin_path = os.path.normpath(
                                    os.path.abspath(__file__) + '../../../builtin_packages')
                if G.first_pass:
                    if G.get_node_attr(module_exports_objs[0]).get('unresolved') == True:
                        if file_ast_node is not None:
                            # rerun the file
                            logger.info('module.exports {} is unresolved, rerun the file...'.format(module_exports_objs[0]))
                            G.file_stack.append(G.get_node_file_path(file_ast_node))
                            empty_rough_stacks(G, reason='handle_require') # don't use this here
                            G.file_stack.pop()
                            module_exports_objs = run_toplevel_file(G, file_ast_node)
                        else:
                            logger.error('Error: module.exports {} is unresolved but file AST node is unknown'.format(module_exports_objs[0]))
                if file_path != 'built-in' and \
                        not file_path.startswith(builtin_path) and G.run_all:
                    run_exported_functions(G, module_exports_objs, extra,
                        file_path=G.get_node_file_path(file_ast_node))
            else:
                logger.error("Required module {} at {} not found!".format(
                    module_name, file_path))
                if file_ast_node is not None:
                    module_exports_objs = \
                        [G.add_obj_node(js_type=None, value=wildcard)]
        
    returned_objs = list(returned_objs)

    # for a require call, we need to run traceback immediately
    # if G.exit_when_found: # moved to run_exported
    #     vul_type = G.vul_type
    #     res_path = traceback(G, vul_type)
    #     res_path = vul_checking(G, res_path[0], vul_type)
    #     if len(res_path) != 0 and G.vul_type != 'proto_pollution':
    #         G.finished = True
    return NodeHandleResult(obj_nodes=returned_objs,
                            used_objs=list(chain(*src)))

def get_module_exports(G, file_path):
    # toplevel_nodes = G.get_nodes_by_type_and_flag('AST_TOPLEVEL', 'TOPLEVEL_FILE')
    toplevel_nodes = G.toplevel_file_nodes
    module_exports_objs = None
    ast_node = None
    for node in toplevel_nodes:
        # print('checking', node, G.get_node_attr(node).get('name'))
        if G.get_node_attr(node).get('name') == file_path:
            # if a file has been required, skip the run and return
            # the saved module.exports
            saved_module_exports = G.get_node_attr(node).get('module_exports')
            ast_node = node
            if saved_module_exports != None:
                module_exports_objs = saved_module_exports
                logger.log(ATTENTION, 'File has been required, '
                    'return saved module.exports {} for {}'
                    .format(module_exports_objs, file_path))
                break
            else:
                module_exports_objs = run_toplevel_file(G, node)
                G.set_node_attr(node,
                    ('module_exports', module_exports_objs))
                break
    return module_exports_objs, ast_node

def run_exported_functions(G, module_exports_objs, extra, file_path):
    # In module mode, file stack:
    # [stdin/helper file, entry file, ...]
    # Because files will be popped before run_exported_functions starts,
    # when the file stack has two or more files (including stdin/helper),
    # it is file-based.
    if G.no_file_based and len(G.file_stack) > 1: # ignore file-based
        return

    if (G.two_pass and not G.first_pass and len(G.file_stack) > 1 and
            not G.no_file_based and file_path not in G.vul_files):
        print(file_path, G.file_stack, 'exports skipped')
        return

    G.file_stack.append(file_path)
    _previous_dont_quit = G.dont_quit
    G.dont_quit = False
    exported_objs = list(module_exports_objs)
    # object names (or expressions to get the objects)
    exported_obj_names = ['module.exports'] * len(exported_objs)
    # Roots are the first functions that needs to be call to reach the
    # current function, used to build control flow paths from it to the
    # source function that can reach the sink function.
    roots = [None] * len(exported_objs)
    # EXIT nodes of the previous function in CF paths described above
    prev_exit_nodes = [None] * len(exported_objs)
    parents = [None] * len(exported_objs)

    tried = set(exported_objs) # objects that have been tried

    def _find_props(parent_obj, parent_obj_name):
        '''
        Find properties under an object.
        '''
        nonlocal G, tried
        proto_objs = \
            G.get_prop_obj_nodes(parent_obj=parent_obj, prop_name='__proto__')
        result_objs = []
        result_obj_names = []
        for name_node in G.get_prop_name_nodes(parent_obj):
            name = G.get_node_attr(name_node).get('name') or '?'
            if name in ['__proto__', 'prototype', 'constructor']: continue
            obj_nodes = G.get_obj_nodes(name_node)
            for obj in obj_nodes:
                if obj in tried: continue
                result_objs.append(obj)
                result_obj_names.append(f'{parent_obj_name}.{name}')
        for proto_obj in proto_objs:
            if proto_obj not in G.builtin_prototypes:
                for name_node in G.get_prop_name_nodes(proto_obj):
                    name = G.get_node_attr(name_node).get('name') or '?'
                    if name in ['__proto__', 'prototype', 'constructor']:
                        continue
                    obj_nodes = G.get_obj_nodes(name_node)
                    for obj in obj_nodes:
                        if obj in tried: continue
                        result_objs.append((parent_obj, obj))
                        # result_obj_names.append(f'{cur_obj_name}.{name}')
                        result_obj_names.append(
                            f'{parent_obj_name}.__proto__.{name}')
            # Promises
            if proto_obj == G.promise_prototype:
                executors = G.get_node_attr(parent_obj).get('executors')
                if executors:
                    for executor in executors:
                        if executor in tried: continue
                        result_objs.append((parent_obj, executor))
                        result_obj_names.append(
                            f'{parent_obj_name}.then()')
        return result_objs, result_obj_names

    while(len(exported_objs) != 0): # BFS
        # print('??!!! first pass =', G.first_pass, exported_objs, exported_obj_names)
        obj = exported_objs.pop(0) # head object
        cur_obj_name = exported_obj_names.pop(0) # head object name
        prev_exit_node = prev_exit_nodes.pop(0) # previous EXIT node of head
        cur_root = roots.pop(0) # root of head
        cur_parent = parents.pop(0)
        parent_obj = None
        if type(obj) == type((1,2)): # if head is a tuple, extract parent obj
            parent_obj = obj[0]
            obj = obj[1]

        # if G.two_pass and not G.first_pass:
        #     if obj not in G.allowed_exported_funcs:
        #         continue

        # ignore built-in functions
        if 'pythonfunc' in G.get_node_attr(obj):
            continue
        # limit entry function by name (if set by command line arguments)
        if G.func_entry_point is not None and not (
            G.get_node_attr(obj).get('type') == 'function' and (
            G.get_node_attr(obj).get('name') == G.func_entry_point
            or cur_obj_name == G.func_entry_point)):
            continue

        if G.first_pass and G.get_node_attr(obj).get('unresolved') == True:
            logger.warning('Exported obj {} is unresolved'.format(obj))
            r = G.get_node_attr(obj).get('how_to_resolve')
            new_vector = (r[0], r[1], None, r[2], r[3], G.file_stack[-1], 2)
            if new_vector in reversed(G.stack1): # avoid duplicated entries
                logger.warning('Vector {} already in stack 1. Call stack: {}'
                    .format(new_vector, G.call_stack))
            else:
                G.stack1.append(new_vector)
            empty_rough_stacks(G, reason='run_exported_functions1')
            returned_objs, created_objs = \
                call_func_obj(G, r[0], r[2], r[3], func_name=r[1])[:2]
            def _filter_objs(o):
                nonlocal G, tried
                if o in tried: return False
                if G.get_node_attr(o).get('unresolved'):
                    logger.error('Object {} is still unresolved!'.format(obj))
                    return False
            returned_objs = list(filter(_filter_objs, returned_objs))
            exported_objs.extend(returned_objs)
            exported_obj_names.extend([cur_obj_name] * len(returned_objs))
            prev_exit_nodes.extend([prev_exit_node] * len(returned_objs))
            roots.extend([cur_root] * len(returned_objs))
            parents.extend([cur_parent] * len(returned_objs))
            tried.update(returned_objs)
            created_objs = list(filter(_filter_objs, created_objs))
            exported_objs.extend(created_objs)
            exported_obj_names.extend([f'({cur_obj_name})()'] * len(created_objs))
            prev_exit_nodes.extend([prev_exit_node] * len(created_objs))
            roots.extend([cur_root] * len(created_objs))
            parents.extend([cur_parent] * len(created_objs))
            tried.update(created_objs)
            continue

        _objs, _names = _find_props(obj, cur_obj_name)
        exported_objs.extend(_objs)
        exported_obj_names.extend(_names)
        prev_exit_nodes.extend([prev_exit_node] * len(_objs))
        roots.extend([cur_root] * len(_objs))
        parents.extend([cur_parent] * len(_objs))
        tried.update(_objs)

        # save current IPT & PP sets before running the function
        old_ipt_write = set(G.ipt_write) # not used
        old_ipt_use = set(G.ipt_use)
        # ↓ not used becase now we use offline detection
        # old_pp = set(G.proto_pollution)

        if obj in G.require_obj_stack:
            continue
        G.require_obj_stack.append(obj)
        newed_objs = None
        newed_obj_names = None
        if G.get_node_attr(obj).get("init_run") is not None:
            continue
        if G.get_node_attr(obj).get('type') != 'function':
            continue
        logger.log(ATTENTION, 'Run exported function {} {}'.format(obj, cur_obj_name))
        G.cur_source_name = cur_obj_name
        # func_timeout may cause threading problems
        G.time_limit_reached = False
        G.func_start_time = time.time()
        # G.cur_fake_args = set() # don't clear the fake arg set
        if G.first_pass:
            G.stack2.append((obj, cur_obj_name, None, [], None, G.file_stack[-1]))
            empty_rough_stacks(G, reason='run_exported_functions2')
        if parent_obj is None:
            # if the function is not a method, try it as a constructor
            # (both instantiated object and return values will be returned)
            # returned_result, newed_objs = call_function(G, [obj],
            #     extra=extra, is_new=True, mark_fake_args=True)
            returned_objs, newed_objs, used_objs, func_run, func_skipped = \
                call_func_obj(G, obj, extra=extra, is_new=True,
                    mark_fake_args=True, dont_skip=True)
            returned_result = NodeHandleResult(obj_nodes=list(returned_objs),
                used_objs=list(used_objs), terminated=func_skipped)
        else:
            # if the function is a method, run it with "this" set to its
            # parent object
            # returned_result, newed_objs = call_function(G, [obj],
            #     this=NodeHandleResult(obj_nodes=[parent_obj]),
            #     extra=extra, mark_fake_args=True)
            returned_objs, newed_objs, used_objs, func_run, func_skipped = \
                call_func_obj(G, obj, _this=NodeHandleResult(obj_nodes=[parent_obj]),
                extra=extra, mark_fake_args=True, dont_skip=True)
            returned_result = NodeHandleResult(obj_nodes=list(returned_objs),
                used_objs=list(used_objs), terminated=func_skipped)
        G.set_node_attr(obj, ('init_run', "True"))

        logger.log(ATTENTION, 'Exported objs: {}'.format(exported_objs))
        # bound functions (bind)
        target_func = G.get_node_attr(obj).get('target_func')
        if target_func is not None:
            obj = target_func

        cur_func_ast = G.get_obj_def_ast_node(obj, aim_type='function')
        cur_entry_node = G.get_successors(cur_func_ast, edge_type='ENTRY')[0]
        cur_exit_node = G.get_successors(cur_func_ast, edge_type='EXIT')[0]
        # if prev_exit_node is not None:
        #     G.add_edge_if_not_exist(
        #         prev_exit_node, cur_entry_node, {"type:TYPE": "FLOWS_TO"})

        # include instantiated objects
        if newed_objs is None:
            newed_objs = [obj]
            newed_obj_names = [cur_obj_name]
        else:
            newed_obj_names = [f'(new {cur_obj_name}())'] * len(newed_objs)
        exported_objs.extend(newed_objs)
        exported_obj_names.extend(newed_obj_names)
        prev_exit_nodes.extend([cur_exit_node] * len(newed_objs))
        roots.extend([cur_root or cur_func_ast] * len(newed_objs))
        parents.extend([cur_func_ast] * len(newed_objs))

        # also include returned objects
        if returned_result is not None:
            exported_objs.extend(returned_result.obj_nodes)
            exported_obj_names.extend(
                [f'{cur_obj_name}()'] * len(returned_result.obj_nodes))
            prev_exit_nodes.extend(
                [cur_exit_node] * len(returned_result.obj_nodes))
            roots.extend(
                [cur_root or cur_func_ast] * len(returned_result.obj_nodes))
            parents.extend([cur_func_ast] * len(returned_result.obj_nodes))

        if cur_parent is not None:
            G.add_edge_if_not_exist(
                cur_parent, cur_func_ast, {"type:TYPE": "RUNS_BEFORE"})

        # prepare some strings for vulnerability log
        func_ast = G.get_obj_def_ast_node(obj, aim_type='function')
        param_list = G.get_child_nodes(func_ast, edge_type='PARENT_OF',
            child_type='AST_PARAM_LIST')
        params = G.get_ordered_ast_child_nodes(param_list)
        arg_names = filter(lambda x: x is not None,
            (G.get_name_from_child(param) for param in params))
        args = ','.join(arg_names)

        # rough control flow check
        # if G.first_pass:
        from .vul_func_lists import signature_lists
        if G.vul_type in signature_lists:
            if not (G.two_pass and not G.first_pass):
                # if not second pass in two-pass analysis
                if not cf_search_complete(
                        G, cur_func_ast, cur_obj_name, cur_root, file_path):
                    if G.first_pass:
                        # we don't detect vulnerabilities in the first pass
                        # however, we detect vulnerabilities in single-pass
                        # (traditional) analysis
                        continue

        if G.two_pass and G.first_pass:
            if G.finished:
                break
            else:
                continue

        # detect vulnerabilities
        vul_type = G.vul_type

        if vul_type not in ['proto_pollution', 'int_prop_tampering']:
            res_path = traceback(G, vul_type)
            res_path = vul_checking(G, res_path[0], vul_type)
            if len(res_path) != 0:
                with open('vul_func_names.csv', 'a') as fp:
                    logger.log(ATTENTION, f'{vul_type} successfully found in '
                               f'{G.entry_file_path} at {cur_obj_name}({args})')
                    fp.write(f'{vul_type},"{G.entry_file_path}","{cur_obj_name}","{args}",{len(res_path)}\n')
                G.success_detect = True
                if G.exit_when_found:
                    G.finished = True
                    # break

        if G.check_proto_pollution:
            # set subtraction, only keep new results
            pps = check_pp(G) - G.proto_pollution
            if pps: # if there are new results
                with open('vul_func_names.csv', 'a') as fp:
                    logger.log(ATTENTION, f'proto_pollution found in {G.entry_file_path} at {cur_obj_name}({args})')
                    fp.write(f'proto_pollution,"{G.entry_file_path}","{cur_obj_name}","{args}",{len(pps)}\n')
                G.proto_pollution.update(pps)
                if G.vul_type == 'proto_pollution' and G.exit_when_found:
                    G.success_detect = True
                    G.finished = True
                    # break
                else:
                    G.finished = False
            # else:
            #     G.finished = False

        if G.check_ipt:
            ipts = G.ipt_use - old_ipt_use
            if ipts: # if there are new results
                with open('vul_func_names.csv', 'a') as fp:
                    logger.log(ATTENTION, f'int_prop_tampering found in {G.entry_file_path} at {cur_obj_name}({args})')
                    fp.write(f'int_prop_tampering,"{G.entry_file_path}","{cur_obj_name}","{args}",{len(ipts)}\n')
                if G.vul_type == 'int_prop_tampering' and G.exit_when_found:
                    G.success_detect = True
                    G.finished = True
                    # break
        
        if G.finished:
            break

    G.dont_quit = _previous_dont_quit
    G.file_stack.pop()

def cf_dfs(G: Graph, current, path=[], targets=[],
           reachable=None, finished=None, nop=None, cg_nodes=None):
    from .vul_func_lists import signature_lists
    if reachable is None:
        reachable = set()
        finished = set()
    if nop is None:
        nop = defaultdict(int)
    if current in reachable:
        yield path + ['REACHABLE']
        reachable.update(path) # memorize
        return
    if current in finished:
        return
    if targets:
        if current in targets:
            yield path
            reachable.update(path) # memorize
            nop[current] = 1
            return
    else: # target is sink functions specific to the vulnerability type
        if G.get_node_attr(current).get('type') == 'CFG_FUNC_ENTRY':
            func_ast = G.get_in_edges(current, edge_type='ENTRY')[0][0]
            objs = G.get_func_decl_objs_by_ast_node(func_ast)
            if objs:
                func_name = G.get_node_attr(objs[0]).get('name')
                if func_name in signature_lists[G.vul_type]:
                    yield path
                    reachable.update(path) # memorize
                    nop[current] = 1
                    return
    cf_edges = G.get_out_edges(current, edge_type='FLOWS_TO')
    cf_edges.sort(key=lambda e: e[2]) # sort by index (timestamp)
    next_nodes = list(dict.fromkeys( # avoid duplicate edges
                    map(lambda e: e[1], cf_edges)))
    func_next_nodes = [] # go to called functions first
    other_next_nodes = []
    for node in next_nodes:
        if (node not in path or
                G.get_node_attr(current).get('type') == 'CFG_FUNC_EXIT'):
            # usually we don't go to visited node,
            # except when a function returns
            if G.get_node_attr(node).get('type') == 'CFG_FUNC_ENTRY':
                _ast = G.get_in_edges(node, edge_type='ENTRY')[0][0]
                if cg_nodes is None or _ast in cg_nodes:
                    func_next_nodes.append(node)
            else:
                other_next_nodes.append(node)
    if func_next_nodes:
        # Consider function calls first.
        # Strictly follow timestamp to search function calls, one at a time,
        # because the path will eventually go back to this statement
        # (when the function returns).
        # It helps when there are continuous calls e.g. foo.bar().baz(),
        # await (modeled as three funciton calls), or calls in if conditions
        node = func_next_nodes[0]
        yield from cf_dfs(G, node, path + [node], targets,
                          reachable, finished, nop, cg_nodes)
    else:
        for node in other_next_nodes:
            yield from cf_dfs(G, node, path + [node], targets,
                              reachable, finished, nop, cg_nodes)
    if G.get_node_attr(current).get('type') != 'CFG_FUNC_EXIT':
        current_nop = 0
        for node in func_next_nodes + other_next_nodes:
            if node in reachable:
                current_nop += nop[node]
        nop[current] = max(nop[current], current_nop)
    finished.add(current)
    # if not (func_next_nodes or other_next_nodes):
    #     yield path # output unreachable paths, for debugging only


def cg_dfs(G: Graph, current, path=[], targets=[], caller=None,
        reachable=None, finished=None, edge_type='CALLS'):
    from .vul_func_lists import signature_lists
    if G.vul_type not in signature_lists:
        return
    if reachable is None:
        reachable = set()
        finished = set()
    if current in reachable:
        yield path + ['REACHABLE']
        reachable.update(path) # memorize
        return
    if current in finished:
        return
    if targets:
        if current in targets:
            yield path
            reachable.update(path) # memorize
            return
    else: # target is sink functions specific to the vulnerability type
        objs = G.get_func_decl_objs_by_ast_node(current)
        if objs:
            func_name = G.get_node_attr(objs[0]).get('name')
            if func_name in signature_lists[G.vul_type]:
                yield path
                reachable.update(path) # memorize
                return
    call_edges = G.get_out_edges(current, edge_type=edge_type)
    call_edges.sort(key=lambda e: e[2]) # sort by index (timestamp)
    next_nodes = list(dict.fromkeys( # avoid duplicate edges
                    map(lambda e: e[1], call_edges)))
    for node in next_nodes:
        if node in path:
            continue
        yield from cg_dfs(G, node, path + [node], targets, current, reachable, finished, edge_type)
    # don't go back to caller
    # if caller is not None: # go back to caller
    #     yield from cg_dfs(G, caller, path + [caller], targets, None, reachable, finished)
    finished.add(current)
    # if not next_nodes:
    #     yield path # output unreachable paths, for debugging only


def cf_dfs_inside(G: Graph, current, path=[], target=None,
           reachable=None, finished=None, nop=None):
    if reachable is None:
        reachable = set()
        finished = set()
    if nop is None:
        nop = defaultdict(int)
    if current in reachable:
        yield path + ['REACHABLE']
        reachable.update(path) # memorize
        return
    if current in finished:
        return
    if G.get_node_attr(current).get('type') == 'CFG_FUNC_ENTRY':
        if current == target:
            yield path
            reachable.update(path) # memorize
            nop[current] = 1
            G.set_node_attr(current, ('local_dist', 0))
        if len(path) > 1: # avoid quitting at the beginning
            return
    cf_edges = G.get_out_edges(current, edge_type='FLOWS_TO')
    cf_edges.sort(key=lambda e: (e[1], e[2]), reverse=True) # sort by index (timestamp)
    # print('now', current, cf_edges)
    next_nodes = list(dict.fromkeys( # avoid duplicate edges
        filter(lambda n: n not in path, map(lambda e: e[1], cf_edges))))
    dist = G.get_node_attr(current).get('local_dist', 1e10) # infinity
    for node in next_nodes:
        yield from cf_dfs_inside(G, node, path + [node], target,
                                    reachable, finished, nop)
        child_dist = G.get_node_attr(node).get('local_dist')
        if child_dist is not None:
            dist = min(dist, child_dist + 1)
    G.set_node_attr(current, ('local_dist', dist))
    if G.get_node_attr(current).get('type') != 'CFG_FUNC_EXIT':
        current_nop = 0
        for node in next_nodes:
            if node in reachable:
                current_nop += nop[node]
        nop[current] = max(nop[current], current_nop)
    elif target is None:
        yield path
        reachable.update(path) # memorize
        nop[current] = 1
        G.set_node_attr(current, ('local_dist', 0))
    finished.add(current)
    # if not next_nodes:
    #     yield path # output unreachable paths, for debugging only


def cgg_cf_dfs(G: Graph, current, cg_path_nodes=set(), path=[], caller=None,
               targets=[], nop=None, output_nodes=None):
    '''
    Deprecated
    '''
    from .vul_func_lists import signature_lists
    if targets:
        if current in targets:
            yield path
            return
    else: # target is sink functions specific to the vulnerability type
        objs = G.get_func_decl_objs_by_ast_node(current)
        if objs:
            func_name = G.get_node_attr(objs[0]).get('name')
            if func_name in signature_lists[G.vul_type]:
                yield path
                nop[current] = 1
                return
    call_edges = G.get_out_edges(current, edge_type='CALLS')
    call_edges.sort(key=lambda e: e[2]) # sort by index (timestamp)
    next_nodes = list(dict.fromkeys( # avoid duplicate edges
                    map(lambda e: e[1], call_edges)))
    for node in next_nodes:
        if node in path:
            continue
        if node not in cg_path_nodes:
            continue
        yield from cg_dfs(G, node, cg_path_nodes, path + [node], current, targets, nop, output_nodes)
    if caller is not None: # go back to caller
        yield from cg_dfs(G, caller, cg_path_nodes, path + [caller], None, targets, nop, output_nodes)
    # if not next_nodes:
    #     yield path # output unreachable paths, for debugging only

def handle_call(G, ast_node, extra):
    '''
    Handle a call expression (AST_CALL/AST_METHOD_CALL/AST_NEW).
    
    Args:
        G (Graph): graph
        ast_node: the Call/New expression's AST node.
        extra (ExtraInfo): extra information.

    Returns:
        NodeHandleResult: Returned objects and used objects.
    '''
    if G.finished or G.time_limit_reached:
        return NodeHandleResult()

    # handle the callee and parent object (for method calls)
    handled_parent = None
    if G.get_node_attr(ast_node).get('type') == 'AST_METHOD_CALL':
        handled_callee, handled_parent = handle_prop(G, ast_node, None, extra)
    else:
        callee = G.get_ordered_ast_child_nodes(ast_node)[0]
        handled_callee = handle_node(G, callee, extra)

    # require is now handled as a built-in function
    # if handled_callee.name == 'require':
    #     module_exports_objs = handle_require_legacy(G, ast_node)
    #     # print(G.get_name_from_child(ast_node), module_exports_objs, G.get_node_file_path(ast_node))
    #     # run the exported objs immediately
    #     if module_exports_objs and G.run_all:
    #         run_exported_functions(G, module_exports_objs, extra)

    #     # for a require call, we need to run traceback immediately
    #     if G.exit_when_found:
    #         vul_type = G.vul_type
    #         res_path = traceback(G, vul_type)
    #         res_path = vul_checking(G, res_path[0], vul_type)
    #         if len(res_path) != 0:
    #             G.finished = True
    #     return NodeHandleResult(obj_nodes=module_exports_objs,
    #                             used_objs=handled_callee.obj_nodes)

    # handle arguments
    handled_args = []
    arg_list_node = G.get_ordered_ast_child_nodes(ast_node)[-1]
    arg_list = G.get_ordered_ast_child_nodes(arg_list_node)
    for arg in arg_list:
        handled_arg = handle_node(G, arg, extra)
        handled_args.append(handled_arg)

    # typeof and detele
    if G.get_node_attr(ast_node).get('flags:string[]') == 'JS_TYPEOF':
        types = defaultdict(lambda: [])
        if handled_args:
            for obj in handled_args[0].obj_nodes:
                if G.get_node_attr(obj).get('type') == 'array':
                    types['object'].append(obj)
                # should we consider wildcard objects' type as 
                # wildcard or fixed "object"?
                elif (G.get_node_attr(obj).get('type') == 'object' and
                    G.get_node_attr(obj).get('code') == wildcard):
                    # types[wildcard].append(obj)
                    types['object'].append(obj)
                    types['string'].append(obj)
                    types['number'].append(obj)
                    types['boolean'].append(obj)
                else:
                    types[G.get_node_attr(obj).get('type')].append(obj)
            for i, val in enumerate(handled_args[0].values):
                if type(val) in ['int', 'float']:
                    types['number'].extend(handled_args[0].value_sources[i])
                elif type(val) == 'str':
                    types['string'].extend(handled_args[0].value_sources[i])
                else:
                    types['object'].extend(handled_args[0].value_sources[i])
        # returned_objs = []
        # used_objs = []
        returned_values = []
        returned_value_sources = []
        for t, sources in types.items():
            # added_obj = G.add_obj_node(ast_node, 'string', t)
            # for s in sources:
            #     add_contributes_to(G, [s], added_obj)
            # returned_objs.append(added_obj)
            # used_objs.extend(sources)
            returned_values.append(t)
            returned_value_sources.append(sources)
        return NodeHandleResult(values=returned_values, 
                                value_sources=returned_value_sources)
    elif G.get_node_attr(ast_node).get('flags:string[]') == 'JS_DELETE':
        if handled_args:
            for name_node in handled_args[0].name_nodes:
                for obj in handled_args[0].obj_nodes:
                    G.remove_all_edges_between(name_node, obj)
        return NodeHandleResult()

    # find function declaration objects
    func_decl_objs = list(filter(lambda x: x != G.undefined_obj and
        x != G.null_obj, handled_callee.obj_nodes))
    func_name = handled_callee.name
    # add blank functions
    if not func_decl_objs:
        if handled_callee.name_nodes:
            for name_node in handled_callee.name_nodes:
                func_decl_obj = G.add_blank_func_with_og_nodes(
                    func_name or '{anonymous}')
                G.add_obj_to_name_node(name_node, tobe_added_obj=func_decl_obj)
                func_decl_objs.append(func_decl_obj)
        else:
            logger.error(f'Function call error: Name node not found for {func_name}!')

    for name_node in handled_callee.name_nodes:
        if G.get_node_attr(name_node).get('statically_declared'):
            G.static_calls.add(ast_node)
        else:
            G.dynamic_calls.add(ast_node)
    # if handled_callee.name_nodes:
    G.total_calls.add(ast_node)

    is_new = False # if the function call is creating a new object
    if G.get_node_attr(ast_node).get('type') == 'AST_CALL':
        stmt_id = 'Call' + ast_node + '-' + get_random_hex()
    elif G.get_node_attr(ast_node).get('type') == 'AST_METHOD_CALL':
        stmt_id = 'Call' + ast_node + '-' + get_random_hex()
        parent = G.get_ordered_ast_child_nodes(ast_node)[0]
    elif G.get_node_attr(ast_node).get('type') == 'AST_NEW':
        stmt_id = 'New' + ast_node + '-' + get_random_hex()
        is_new = True
    else:
        stmt_id = None
    returned_result, created_objs = \
        call_function(G, func_decl_objs, handled_args,
        handled_parent, extra, call_ast=ast_node, is_new=is_new,
        stmt_id=stmt_id, func_name=func_name)
    if is_new:
        returned_result.obj_nodes = created_objs
    # don't build control flow here
    # cpg_node = G.find_nearest_upper_CPG_node(ast_node)
    # for last_stmt in G.last_stmts:
    #     G.add_edge(last_stmt, cpg_node, {'type:TYPE': 'FLOWS_TO'})
    # G.last_stmts = [cpg_node]
    return returned_result

def call_function(G, func_objs, args=[], this=NodeHandleResult(), extra=None,
    call_ast=None, is_new=False, stmt_id='Unknown', func_name=None,
    mark_fake_args=False, python_callback=None, promise_related=False):
    '''
    Call a list of functions.
    
    Args:
        G (Graph): Graph.
        func_objs: List of function declaration objects.
        args (List[NodeHandleResult]): List of handled arguments.
        this (NodeHandleResult): Handled override "this" object.
        extra (ExtraInfo, optional): Extra information. Defaults to
            empty ExtraInfo.
        call_ast (optional): The call expression's AST node. Defaults to
            None.
        is_new (bool, optional): If the caller is a "new" statement.
            Defaults to False.
        stmt_id (str, optional): Caller's statement ID, for branching
            use only. Defaults to 'Unknown'.
        func_name (str, optional): The function's name, for adding blank
            functions only. Defaults to '{anonymous}'.
    
    Returns:
        NodeHandleResult, List: Call result (including returned objects
            and used objects), and list of created objects.
    '''
    if G.finished or G.time_limit_reached:
        return NodeHandleResult(), []


    # No function objects found, return immediately
    if not func_objs:
        logger.error(f'No definition found for function {func_name}')
        return NodeHandleResult(), []

    if extra is None:
        extra = ExtraInfo()

    # process arguments
    # callback_functions = set() # only for unmodeled built-in functions
    # for arg in args:
    #     # add callback functions
    #     for obj in arg.obj_nodes:
    #         if G.get_node_attr(obj).get('type') == 'function':
    #             callback_functions.add(obj)
    # callback_functions = list(callback_functions)


    # if the function declaration has multiple possibilities,
    # and need to merge afterwards
    has_branches = (len(func_objs) > 1 and not G.single_branch)

    # process function name
    if not func_name:
        if func_objs:
            func_name = G.get_node_attr(func_objs[0]).get('name')
    if not func_name:
        func_name = '{anonymous}'

    if stmt_id == 'Unknown' and call_ast is not None:
        stmt_id = call_ast

    # auto exploit
    attack_dict = {
        'os_command': ['""; touch exploited &', '"; touch exploited #', '& touch exploited #', "''; touch exploited #"],
        'code_exec': [';console.log("exploited");//', ',console.log("exploited");//', '0;console.log("exploited");//'],
        'nosql': ['exploited'],
        'path_traversal': ['../exploited', '../../exploited'],
        'xss': ['exploited'],
    }
    if ((G.auto_exploit and not G.first_pass) and (
            func_name and func_name in signature_lists[G.vul_type] and args)):
        for payload in attack_dict.get(G.vul_type):
            handled_arg = args[0]
            logger.info(sty.ef.b + '[AUTO] Constraint solver is solving for {}...'.format(G.cur_source_name) + sty.rs.all)
            G.solve_from = payload # payload string
            solution = solver.solve(G, handled_arg.obj_nodes, None,
                                    contains=True)
            for i, (assertions, results) in enumerate(solution):
                logger.debug(f'{sty.ef.inverse}Constraints #{i+1}:{sty.rs.all}')
                logger.debug(assertions)      
                if results == 'failed':
                    logger.warning(f'Attempt #{i+1} failed.')
                    continue
                elif results == 'timeout':
                    logger.warning(f'Attempt #{i+1} timed out.')
                    continue
                logger.info(f'{sty.ef.inverse}Results #{i+1}:{sty.rs.all}')
                if results:
                    success = False
                    for k, (name, v) in results.items():
                        if G.get_node_attr(k[1:]).get('fake_arg'):
                            if G.solve_from in str(v) or str(v) in G.solve_from:
                                success = True
                                G.success_exploit = True
                            logger.info(f'{sty.fg.green}{sty.ef.b}INPUT{sty.rs.ef} {name}({k}){sty.rs.all} = {v}')
                        elif k[1:] in handled_arg.obj_nodes:
                            logger.info(f'{sty.ef.b}SINK{sty.rs.all} {name}({k}) = {v}')
                        else:
                            logger.info(f'{name}({k}) = {v}')
                    if success:
                        logger.info(sty.fg.green + '[AUTO] Successfully found solution!' + sty.rs.all)
                    else:
                        logger.warning(f'[AUTO] Solving may have failed. Please check logs.')
                    # logger.info(f'Current arguments: {G.cur_fake_args}')
                else:
                    logger.debug('No result.')
            G.solve_from = None
        if G.interactive:
            input('Press Enter to continue...')

    # initiate return values
    returned_objs = set()
    used_objs = set()
    created_objs = []
    returned_values = [] # for python function only
    returned_value_sources = [] # for python function only
    exit_nodes = set() # build control flows

    # initiate fake return objects (only create once)
    fake_returned_objs = []
    fake_created_objs = []

    # if any function is run in this call
    any_func_run = False
    # if any function is skipped in this call
    any_func_skipped = False
    
    # manage branches
    branches = extra.branches
    parent_branch = branches.get_last_choice_tag()

    # call the Python callback function
    if python_callback is not None:
        python_callback(G)

    G.affected_name_nodes.append(set())
    # for each possible function declaration
    for i, func_obj in enumerate(func_objs):
        branch_returned_objs, branch_created_objs, branch_used_objs, \
        func_run, func_skipped = call_func_obj(
            G, func_obj, args, this, extra, call_ast,
            is_new, has_branches, stmt_id, func_name,
            mark_fake_args, python_callback, i,
            returned_values, returned_value_sources, exit_nodes,
            fake_returned_objs, fake_created_objs,
            promise_related=promise_related)
        any_func_run = any_func_run or func_run 
        any_func_skipped = any_func_skipped or func_skipped 
        # if func_run and not func_skipped:
        if branch_returned_objs is not None:
            returned_objs.update(branch_returned_objs)
            created_objs.extend(branch_created_objs)
            used_objs.update(branch_used_objs)

    if has_branches and not G.single_branch and any_func_run:
        merge(G, stmt_id, len(func_objs), parent_branch)
    if len(G.affected_name_nodes) > 1:
        G.affected_name_nodes[-2].update(G.affected_name_nodes[-1])
    G.affected_name_nodes.pop()

    if not any_func_run and not G.first_pass:
        logger.error('Error: No function was run during this function call')

    # G.last_stmts = exit_nodes
    if call_ast is not None:
        caller_cpg = G.find_nearest_upper_CPG_node(call_ast)
        for exit_node in exit_nodes:
            G.add_edge_if_not_exist(exit_node, caller_cpg, {'type:TYPE': 'FLOWS_TO'})
        G.last_stmts = [caller_cpg]
    else:
        G.last_stmts = []

    return NodeHandleResult(obj_nodes=list(returned_objs),
            used_objs=list(used_objs),
            values=returned_values, value_sources=returned_value_sources,
            terminated=any_func_skipped
        ), created_objs

def js_eval(G: Graph, exp, extra=ExtraInfo()):
    root_node = str(G.cur_id)
    result = None
    try:
        analyze_string(G, exp, start_node_id=G.cur_id, expression=True)
        result = handle_node(G, root_node, extra)
        result.ast_node = root_node
    except Exception as e:
        logger.debug(tb.format_exc())
        logger.error(e)
        result = NodeHandleResult(value=[wildcard])
    return result

def handle_eval(G: Graph, caller_ast, extra, _, strings, *args):
    returned_values = []
    returned_value_sources = []
    returned_objs = []
    used_objs = []
    num_of_branches = 0
    branches = extra.branches
    G.affected_name_nodes.append(set())
    for i, value in enumerate(strings.values):
        if type(value) == str and value != wildcard:
            if not G.single_branch:
                branches = branches + [BranchTag(
                    point=f'Eval{caller_ast}', branch=num_of_branches)]
                num_of_branches += 1
            result = js_eval(G, value, ExtraInfo(branches=branches))
            returned_values.extend(result.values)
            returned_value_sources.extend(result.value_sources)
            returned_objs.extend(result.obj_nodes)
            used_objs.extend(strings.value_sources[i])
        else:
            returned_values.append(value)
            returned_value_sources.append(strings.value_sources[i])
            # workaround for new trace rule? (data flow needs to be built)
            used_objs.extend(strings.value_sources[i])
    for obj in strings.obj_nodes:
        value = G.get_node_attr(obj).get('code')
        if value == wildcard or G.get_node_attr(obj).get('type') == 'string':
            value = G.get_node_attr(obj).get('code')
            if not G.single_branch:
                branches = branches + [BranchTag(
                    point=f'Eval{caller_ast}', branch=num_of_branches)]
                num_of_branches += 1
            if value == wildcard:
                result = NodeHandleResult(values=[wildcard],
                                          value_sources=[obj])
            else:
                result = js_eval(G, value, ExtraInfo(branches=branches))
            returned_values.extend(result.values)
            returned_value_sources.extend(result.value_sources + [obj])
            returned_objs.extend(result.obj_nodes)
            used_objs.append(obj)
        else:
            returned_objs.append(obj)
    if not G.single_branch:
        merge(G, f'Eval{caller_ast}', num_of_branches,
            parent_branch=branches.get_last_choice_tag())
    if len(G.affected_name_nodes) > 1:
        G.affected_name_nodes[-2].update(G.affected_name_nodes[-1])
    G.affected_name_nodes.pop()
    for arg in args: # for test use only, eval shouldn't have so many args
        used_objs.extend(chain(*(arg.value_sources)))
        used_objs.extend(arg.obj_nodes)
    return NodeHandleResult(obj_nodes=returned_objs, used_objs=used_objs,
        values=returned_values, value_sources=returned_value_sources)

def get_df_callback(G, ast_node=None):
    if ast_node is None:
        cpg_node = G.cur_stmt
    else:
        cpg_node = G.find_nearest_upper_CPG_node(ast_node)
    # print('cpg node =', cpg_node, ast_node)
    return lambda result: build_df_by_def_use(G, cpg_node, result.used_objs)

def build_df_by_def_use(G, cur_stmt, used_objs):
    """
    Build data flows for objects used in current statement.
    The flow will be from the object's definition to current statement (current node).
    """
    if not used_objs or cur_stmt is None:
        return
    if G.first_pass:
        return
    start_time = time.time()
    cur_lineno = G.get_node_attr(cur_stmt).get('lineno:int')
    # If an used object is a wildcard object, add its parent object as
    # used object too, until it is not a wildcard object.
    used_objs = list(used_objs)
    used_obj_set = set(used_objs)
    for obj in used_objs:
        node_attrs = G.get_node_attr(obj)
        if node_attrs.get('type') == 'object' and node_attrs.get('code') == wildcard:
            for e1 in G.get_in_edges(obj, edge_type='NAME_TO_OBJ'):
                for e2 in G.get_in_edges(e1[0], edge_type='OBJ_TO_PROP'):
                    if e2[0] not in used_obj_set:
                        used_objs.append(e2[0])
                        used_obj_set.add(e2[0])
                        # logger.debug("{}-----{}-----{}".format(obj, e1[0], e2[0]))
    for obj in used_objs:
        def_ast_node = G.get_obj_def_ast_node(obj)
        # print("?", cur_stmt, used_objs, def_ast_node)
        if def_ast_node is None: continue
        def_cpg_node = G.find_nearest_upper_CPG_node(def_ast_node)
        if def_cpg_node is None: continue
        if def_cpg_node == cur_stmt: continue
        def_lineno = G.get_node_attr(def_cpg_node).get('lineno:int')
        logger.info(sty.fg.li_magenta + sty.ef.inverse + "OBJ REACHES" + sty.rs.all +
        " {} -> {} (Line {} -> Line {}), by OBJ {}".format(def_cpg_node,
        cur_stmt, def_lineno, cur_lineno, obj))
        G.add_edge(def_cpg_node, cur_stmt, {'type:TYPE': 'OBJ_REACHES', 'obj': obj})
    # if time.time() - start_time > 0.1:
    #     print('df time = %.3f, %d' % (time.time() - start_time, len(used_objs)))

def print_handle_result_colored(G: Graph, handle_result: NodeHandleResult):
    def color_node(n):
        if G.get_node_attr(n).get('tainted'):
            return sty.fg.li_red + n + sty.rs.all
        elif n in G.inv_internal_objs:
            return sty.ef.inverse + n + sty.rs.all
        elif n in G.builtin_prototypes:
            return sty.fg.li_yellow + n + sty.rs.all
        else:
            return n
    show_tainted = lambda l: '[' + ', '.join([color_node(n) for n in l]) + ']'
    output = f'{sty.ef.b}{sty.fg.cyan}{handle_result.ast_node}{sty.rs.all} ' \
        f'handle result: obj_nodes={show_tainted(handle_result.obj_nodes)}'
    if handle_result.name_tainted:
        output += f', {sty.fg.li_red}name={handle_result.name}{sty.rs.all}'
    else:
        output += f', name={handle_result.name}'
    output += f', name_nodes={handle_result.name_nodes}'
    if handle_result.values:
        output += f', values={handle_result.values}'
    if handle_result.used_objs:
        output += f', used_objs={show_tainted(handle_result.used_objs)}'
    if handle_result.parent_is_proto:
        output += f', parent_is_proto={handle_result.parent_is_proto}'
    covered_stmt = len(G.covered_stat)
    total_stmt = G.get_total_num_statements()
    output += f'\n{sty.fg.li_yellow}Code coverage:{sty.rs.all} {covered_stmt / total_stmt * 100:.2f}%'
    output += f' {covered_stmt}/{total_stmt}'
    # if handle_result.from_branches:
    #     output += f'{sty.fg.da_grey}, from_branches=' \
    #         f'{handle_result.from_branches}{sty.rs.all}'
    logger.debug(output)
    # for o in handle_result.obj_nodes:
    #     print(o, G.get_node_attr(o))

    if handle_result.ast_node:
        ast_node = handle_result.ast_node
        for obj in handle_result.obj_nodes:
            G.add_edge(handle_result.ast_node, obj,
                {'type:TYPE': 'REFERS_TO', 'scope': G.cur_scope})
        for name_node in handle_result.name_nodes:
            G.add_edge(handle_result.ast_node, name_node,
                {'type:TYPE': 'REFERS_TO', 'scope': G.cur_scope})
        G.last_handled = ast_node
        lineno = G.get_node_attr(ast_node).get('lineno:int')
        if lineno not in [None, '']:
            G.last_handled_lineno = lineno
    
    if handle_result.name:
        for obj in handle_result.obj_nodes:
            G.reverse_names[obj].add(handle_result.name)

def print_handle_result(G: Graph, handle_result: NodeHandleResult):
    output = f'{sty.ef.b}{sty.fg.cyan}{handle_result.ast_node}{sty.rs.all} ' \
        f'handle result: obj_nodes={handle_result.obj_nodes}, ' \
        f'name={handle_result.name}, name_nodes={handle_result.name_nodes}'
    if handle_result.values:
        output += f', values={handle_result.values}'
    if handle_result.used_objs:
        output += f', used_objs={handle_result.used_objs}'
    if handle_result.name_tainted:
        output += f', name_tainted={handle_result.name_tainted}'
    # if handle_result.from_branches:
    #     output += f'{sty.fg.da_grey}, from_branches=' \
    #         f'{handle_result.from_branches}{sty.rs.all}'
    logger.debug(output)

    if handle_result.ast_node:
        ast_node = handle_result.ast_node
        for obj in handle_result.obj_nodes:
            G.add_edge(handle_result.ast_node, obj,
                {'type:TYPE': 'REFERS_TO', 'scope': G.cur_scope})
        for name_node in handle_result.name_nodes:
            G.add_edge(handle_result.ast_node, name_node,
                {'type:TYPE': 'REFERS_TO', 'scope': G.cur_scope})
        G.last_handled = ast_node
        lineno = G.get_node_attr(ast_node).get('lineno:int')
        if lineno not in [None, '']:
            G.last_handled_lineno = lineno

    if handle_result.name:
        for obj in handle_result.obj_nodes:
            G.reverse_names[obj].add(handle_result.name)

def generate_obj_graph(G: Graph, entry_nodeid):
    """
    generate the object graph of a program
    """
    G.setup1()
    modeled_js_builtins.setup_js_builtins(G)
    G.setup2()
    if G.print:
        NodeHandleResult.print_callback = lambda x: print_handle_result_colored(G, x)
    else:
        NodeHandleResult.print_callback = lambda x: print_handle_result(G, x)
    # print('now the graph has', G.graph.number_of_nodes())
    logger.info(sty.fg.green + "GENERATE OBJECT GRAPH" + sty.rs.all + ": " + entry_nodeid)
    # obj_nodes = G.get_nodes_by_type("AST_FUNC_DECL")
    # for node in obj_nodes:
    #     register_func(G, node[0])
    if G.rough_call_dist and not G.first_pass:
        build_rough_call_graph(G, entry_nodeid)
    handle_node(G, entry_nodeid)
    # add_edges_between_funcs(G)
    if G.first_pass:
        empty_rough_stacks(G, reason='generate_obj_graph')
        logger.info('Running CF path search again...')
        for item in G.cf_searches:
            cf_search_complete(G, *item)
    G.finished_num_of_passes += 1

def analyze_files(G, path, start_node_id=0, check_signatures=[]):
    """
        return we generate the obj graph or not
    """
    result = esprima_parse(path, ['-n', str(start_node_id), '-o', '-'],
        print_func=logger.info)
    G.import_from_string(result)
    if not G.check_signature_functions(check_signatures):
        return -1
    first_pass_time = 0
    second_pass_time = 0

    if G.two_pass or G.coarse_only:
        G.first_pass = True
        single_branch = G.single_branch
        G.single_branch = False
        logger.info(sty.fg.green + sty.ef.b + "1st run starts..." + sty.rs.all)
        time1 = time.time()
        generate_obj_graph(G, str(start_node_id))
        logger.info(sty.fg.green + sty.ef.b + "1st run finished in {:.2f}s. "
            .format(time.time() - time1) + sty.rs.all)
        first_pass_time = time.time() - time1
    if G.two_pass:
        if not G.possible_cf_nodes:
            logger.warning('No CF paths found, 2nd run skipped.')
            log_cf(G, first_pass_time, second_pass_time)
            return -2
        cf_edges = G.get_edges_by_types(['FLOWS_TO', 'CALLS', 'ENTRY', 'EXIT']) 
        cf_edges = list(filter(lambda e: int(e[0]) < G.num_of_ast_nodes and
            int(e[1]) < G.num_of_ast_nodes, cf_edges))
        G.clear() # reset the graph
        G.import_from_string(result) # import AST again
        G.add_edges_from_list(cf_edges)
        G.single_branch = single_branch
        logger.info(sty.fg.green + sty.ef.b
            + "Starting 2nd run..." + sty.rs.all)
    if not G.coarse_only:
        G.first_pass = False
        time2 = time.time()
        generate_obj_graph(G, str(start_node_id))
        logger.info(sty.fg.green + sty.ef.b + "2nd run finished in {:.2f}s. "
            .format(time.time() - time2) + sty.rs.all)
        second_pass_time = time.time() - time2 - G.solver_time
    log_cf(G, first_pass_time, second_pass_time)
    return 1

def analyze_string(G, source_code, start_node_id=None, generate_graph=False,
    expression=False):
    first_pass_time = 0
    second_pass_time = 0

    if start_node_id is None:
        start_node_id = G.cur_id
    args = ['-n', str(start_node_id), '-o', '-']
    if expression:
        args = ['-e'] + args 
    result = esprima_parse('-', args,
        input=source_code, print_func=logger.info)
    G.import_from_string(result)
    if generate_graph:
        if G.two_pass or G.coarse_only:
            G.first_pass = True
            single_branch = G.single_branch
            call_limit = G.call_limit
            G.call_limit = 1
            G.single_branch = False
            logger.info(
                sty.fg.green + sty.ef.b + "1st run starts..." + sty.rs.all)
            time1 = time.time()
            generate_obj_graph(G, str(start_node_id))
            logger.info(sty.fg.green + sty.ef.b + "1st run finished {:.2f}s. "
                .format(time.time() - time1) + sty.rs.all)
            first_pass_time = time.time() - time1
        if G.two_pass:
            if not G.possible_cf_nodes:
                logger.warning('No CF paths found, 2nd run skipped.')
                log_cf(G, first_pass_time, second_pass_time)
                return None
            cf_edges = G.get_edges_by_types(['FLOWS_TO', 'CALLS', 'ENTRY', 'EXIT']) 
            # print(cf_edges)
            # for e in cf_edges:
            #     print(e[0], e[1], e[2])
            #     print(G.get_node_attr(e[0]), G.get_node_attr(e[1]))
            # input()
            cf_edges = list(filter(lambda e: int(e[0]) < G.num_of_ast_nodes and
                int(e[1]) < G.num_of_ast_nodes, cf_edges))
            G.clear() # reset the graph
            G.import_from_string(result) # import AST again
            G.add_edges_from_list(cf_edges)
            G.single_branch = single_branch
            G.call_limit = call_limit
            if G.interactive:
                input('Press Enter to continue...')
            logger.info(sty.fg.green + sty.ef.b
                + "Starting 2nd run..." + sty.rs.all)
        if not G.coarse_only:
            G.first_pass = False
            time2 = time.time()
            generate_obj_graph(G, str(start_node_id))
            logger.info(sty.fg.green + sty.ef.b + "2nd run finished in {:.2f}s. "
                .format(time.time() - time2) + sty.rs.all)
            second_pass_time = time.time() - time2 - G.solver_time
        log_cf(G, first_pass_time, second_pass_time)
    else:
        return str(start_node_id)

def log_cf(G, first_pass_time, second_pass_time):
    # call edges are counted separately below
    cf_edges = G.get_edges_by_types(['FLOWS_TO', 'ENTRY', 'EXIT'])
    real_cf_counter = 0
    for e in cf_edges:
        l0 = G.get_node_attr(e[0]).get('labels:label')
        if l0 is None or l0.startswith('Artificial'):
            continue
        l1 = G.get_node_attr(e[1]).get('labels:label')
        if l1 is None or l1.startswith('Artificial'):
            continue
        real_cf_counter += 1
    call_edges = G.get_edges_by_type('CALLS')
    real_ce_counter = 0
    real_call_edges = []
    promise_related_ce_counter = 0
    for e in call_edges:
        if e[-1].get('promise_related'):
            promise_related_ce_counter += 1
        l0 = G.get_node_attr(e[0]).get('labels:label')
        if l0 is None or l0.startswith('Artificial'):
            continue
        l1 = G.get_node_attr(e[1]).get('labels:label')
        if l1 is None or l1.startswith('Artificial'):
            continue
        real_ce_counter += 1
        real_call_edges.append(e)
    loc = None
    if os.path.isfile(G.entry_file_path):
        loc = len(open(G.entry_file_path, 'rb').readlines())
    eval_logger.info(json.dumps({"file": G.entry_file_path, "type": "time", "pass": "1", "time": first_pass_time}))
    eval_logger.info(json.dumps({"file": G.entry_file_path, "type": "time", "pass": "2", "time": second_pass_time}))
    eval_logger.info(json.dumps({"file": G.entry_file_path, "type": "time", "pass": "3", "time": G.solver_time}))
    eval_logger.info(json.dumps({"file": G.entry_file_path, "type": "time", "pass": "1+2", "time": first_pass_time + second_pass_time, "dynamic_calls": len(G.dynamic_calls), "total_calls": len(G.total_calls), "ast_nodes": G.num_of_ast_nodes, "loc": loc}))
    eval_logger.info(json.dumps({"file": G.entry_file_path, "type": "time", "pass": "1+2+3", "time": first_pass_time + second_pass_time + G.solver_time, "dynamic_calls": len(G.dynamic_calls), "total_calls": len(G.total_calls), "ast_nodes": G.num_of_ast_nodes, "loc": loc}))
    eval_logger.info(json.dumps({"file": G.entry_file_path, "type": "cf",
        "cf": [len(cf_edges), real_cf_counter, len(call_edges), real_ce_counter,
            len(cf_edges)-len(call_edges), real_cf_counter-real_ce_counter, promise_related_ce_counter],
        "calls": [len(G.dynamic_calls), len(G.static_calls), len(G.unresolvable_calls), len(G.total_calls)]}
    ))

def analyze_json(G, json_str, start_node_id=0, extra=None):
    # This function is almost the same as analyze_string,
    # but it is too dirty. I don't want to put them in one function.

    # because esprima cannot directly parse JSON, we add a previx
    # the real JSON object starts at 8 if the File node is at node 0
    # so we pass a "start_node_id - 8" to make the JSON object starts
    # at "start_node_id"
    json_str = 'var a = ' + json_str.strip()
    result = esprima_parse('-', ['-n', str(start_node_id - 8), '-o', '-'],
        input=json_str, print_func=logger.info)
    G.import_from_string(result)
    # remove all nodes and edges before the JSON object
    def filter_func(line):
        try:
            if int(line.split('\t')[0]) < start_node_id:
                return False
            return True
        except ValueError:
            pass
        return True
    result = '\n'.join(filter(filter_func, result.split('\n')))
    G.import_from_string(result)
    return handle_node(G, str(start_node_id), extra)

def analyze_json_python(G: Graph, json_str, extra=None, call_ast=None):
    json_str = str(json_str)
    if json_str is None:
        return None
    try:
        py_obj = json.loads(json_str)
        logger.debug('Python JSON parse result: ' + str(py_obj))
    except json.decoder.JSONDecodeError:
        return None
    return G.generate_obj_graph_for_python_obj(py_obj, ast_node=call_ast)

def handle_var_prop_name(G: Graph, exp, extra=ExtraInfo()) -> NodeHandleResult:
    if '.' in exp:
        parent_name, prop_name = exp.rsplit('.', 1)
        handled_parent = handle_var_prop_name(G, parent_name, extra)
        if prop_name == '*':
            prop_name = wildcard
        parent_objs = list(filter(
            lambda x: x != G.undefined_obj, handled_parent.obj_nodes))
        if not parent_objs:
            logger.error(f"Parent object '{parent_name}' not found!")
            return NodeHandleResult()
        else:
            # find property name nodes and object nodes
            name_nodes, obj_nodes = find_prop(G, parent_objs, 
                prop_name, extra.branches, parent_name)
            name_nodes, obj_nodes = list(name_nodes), list(obj_nodes)
            return NodeHandleResult(obj_nodes=obj_nodes, name_nodes=name_nodes,
                name=exp)
    else:
        name_node = G.get_name_node(exp)
        if name_node is None:
            logger.error(f"Variable '{exp}' not found!")
            return NodeHandleResult()
        else:
            obj_nodes = list(set(
                G.get_objs_by_name_node(name_node, branches=extra.branches)))
            return NodeHandleResult(obj_nodes=obj_nodes,
                name_nodes=[name_node], name=exp)


def find_blocks(G: Graph, ast_node):
    '''
    Find the upper blocks and functions of the caller. Because
    POSSIBLY_CALLS edges are built between blocks (instead of call
    expression or statement) and functions (AST_FUNC_DECL), we need 
    to find which blocks and functions the call expression is in.
    '''        
    node_type = G.get_node_attr(ast_node).get('type')
    if node_type in [
        'AST_FUNC_DECL', 'AST_CLOSURE', 'AST_METHOD', 'AST_STMT_LIST']:
        yield ast_node
    if node_type not in ['AST_FUNC_DECL', 'AST_CLOSURE', 'AST_METHOD']:
        for e in G.get_in_edges(ast_node, edge_type='PARENT_OF'):
            yield from find_blocks(G, e[0])


def find_function(G: Graph, ast_node):
    '''
    Find the upper blocks and functions of the caller. Because
    CALLS edges are built between functions (instead of call
    expression or statement), we need to find which functions the call
    expression is in.
    '''        
    node_type = G.get_node_attr(ast_node).get('type')
    if node_type in [
        'AST_FUNC_DECL', 'AST_CLOSURE', 'AST_METHOD', 'AST_TOPLEVEL']:
        return ast_node
    else:
        for e in G.get_in_edges(ast_node, edge_type='PARENT_OF'):
            return find_function(G, e[0])
        for e in G.get_in_edges(ast_node, edge_type='ENTRY'):
            return find_function(G, e[0])
        for e in G.get_in_edges(ast_node, edge_type='EXIT'):
            return find_function(G, e[0])
    return None

def build_rough_call_graph(G: Graph, entry_node):
    '''
    Preprocess the AST to generate a rough call graph, for caculating
    distances, based on function name matching.

    Args:
        G (Graph): Graph
        entry_node ([type]): Entry node

    Returns:
        This function doesn't return anything. It builds the call graph
        directly on G.
    '''
    if not G.vul_type:
        return
    def get_func_name(G: Graph, ast_node, recursive=True):
        '''
        Get the called function name (for call expression) or function
        name (for function declaration). If the callee is a method of an
        object, it returns the method name only instead of
        parent.method.
        '''
        node_type = G.get_node_attr(ast_node).get('type')
        if node_type in [
            'AST_FUNC_DECL', 'AST_CLOSURE', 'AST_METHOD', 'AST_STMT_LIST']:
            name = G.get_name_from_child(ast_node, order=1, max_depth=2)
            if not name or name == '{anon}':
                if recursive:
                    return get_func_name(G,
                        G.get_in_edges(ast_node, edge_type='PARENT_OF')[0][0])
                else:
                    return None
            else:
                return name
        elif node_type in ['AST_METHOD_CALL', 'AST_PROP']:
            return get_func_name(G, G.get_ordered_ast_child_nodes(ast_node)[1],
                recursive=False)
        elif node_type in ['AST_CALL', 'AST_NEW']:
            return get_func_name(G, G.get_ordered_ast_child_nodes(ast_node)[0],
                recursive=False)
        elif node_type == 'AST_ASSIGN':
            children = G.get_ordered_ast_child_nodes(ast_node)
            if len(children) >= 2:
                left, right = children[:2]
                if G.get_node_attr(right).get('type') in ['AST_FUNC_DECL',
                    'AST_CLOSURE', 'AST_METHOD']:
                    return get_func_name(G, left)
        else:
            return G.get_name_from_child(ast_node)
    logger.debug(sty.fg.magenta + sty.ef.b +
                 'Building rough call graph...' + sty.rs.all)
    dummy_func = G.add_blank_func('dummy')
    G.set_node_attr(dummy_func, ('complexity_score', 0))
    func_dict = {}
    visited = set()
    def dummy_handle_node(G: Graph, ast_node):
        '''
        Handle the node and calculate the complexity scores (number of
        expressions). It only handles some basic node types.
        '''
        nonlocal func_dict, signature_decls, visited
        complexity = 0
        node_type = G.get_node_attr(ast_node).get('type')
        if ast_node in visited:
            return G.get_node_attr(ast_node).get('complexity_score', 1)
        visited.add(ast_node)

        if node_type in ['AST_FUNC_DECL', 'AST_CLOSURE', 'AST_METHOD']:
            children = G.get_child_nodes(ast_node, child_type='AST_STMT_LIST')
            if children:
                complexity = dummy_handle_node(G, children[0])
        elif node_type == 'File':
            for e in list(G.get_out_edges(ast_node, edge_type='FILE_OF')):
                complexity += dummy_handle_node(G, e[1])
        elif node_type == 'Directory':
            for e in list(G.get_out_edges(ast_node, edge_type='DIRECTORY_OF')):
                complexity += dummy_handle_node(G, e[1])
        else:
            for e in list(G.get_out_edges(ast_node, edge_type='PARENT_OF')):
                complexity += dummy_handle_node(G, e[1])
        if node_type in ['AST_CALL', 'AST_METHOD_CALL', 'AST_NEW']:
            # if node_type == 'AST_METHOD_CALL':
            #     func_name = G.get_name_from_child(
            #         G.get_ordered_ast_child_nodes(ast_node)[1])
            # else:
            #     func_name = G.get_name_from_child(ast_node)
            func_name = get_func_name(G, ast_node)
            func_decls = func_dict.get(func_name)
            if func_name == 'require':
                file_path = G.get_node_attr(ast_node).get('name')
                # toplevel_nodes = G.get_nodes_by_type_and_flag(
                #                     'AST_TOPLEVEL', 'TOPLEVEL_FILE')
                toplevel_nodes = G.toplevel_file_nodes
                for f in toplevel_nodes:
                    if G.get_node_attr(f).get('name') == file_path:
                        dummy_handle_node(G, f)
                return 1
            if not func_decls:
                func_decls = []
                for func in G.get_node_by_attr('type', 'AST_FUNC_DECL'):
                    if get_func_name(G, func) == func_name:
                        func_decls.append(func)
                for assign in G.get_node_by_attr('type', 'AST_ASSIGN'):
                    children = G.get_ordered_ast_child_nodes(assign)
                    if len(children) < 2:
                        continue
                    left, right = children[:2]
                    if get_func_name(G, assign) == func_name:
                        if G.get_node_attr(right).get('type') in [
                            'AST_FUNC_DECL', 'AST_CLOSURE', 'AST_METHOD']:
                            func_decls.append(right)
                func_decls = list(set(func_decls))
                if not func_decls:
                    func_decls = [dummy_func]
                func_dict[func_name] = func_decls
            for func in func_decls:
                for block in list(find_blocks(G, ast_node)):
                    G.add_edge(block, func, {'type:TYPE': 'POSSIBLY_CALLS'})
        if node_type in [
            'AST_FUNC_DECL', 'AST_CLOSURE', 'AST_METHOD', 'AST_STMT_LIST']:
            G.set_node_attr(ast_node, ('complexity_score', complexity))
        if node_type in ['AST_FUNC_DECL', 'AST_CLOSURE', 'AST_METHOD']:
            return 0
        return complexity + 1
    dummy_handle_node(G, entry_node)
    from .vul_func_lists import signature_lists
    signature_decls = []
    for signature_name in signature_lists.get(G.vul_type, []):
        if signature_name not in func_dict:
            continue
        signature_decls += func_dict[signature_name]
    q = [(f, 0) for f in signature_decls]
    while q:
        callee, d = q.pop(0)
        if G.get_node_attr(callee).get('distance_to_goal') is not None:
            continue
        G.set_node_attr(callee, ('distance_to_goal', d))
        logger.debug(sty.fg.magenta + sty.ef.b + 'Rough CFG: ' + sty.rs.all +
            f'Block {callee} {get_func_name(G, callee) or "."} '
            f'DISTANCE TO GOAL: {d}, COMPLEXITY SCORE: '
            f'{G.get_node_attr(callee).get("complexity_score")}')
        callers = [e[0]
            for e in G.get_in_edges(callee, edge_type='POSSIBLY_CALLS')]
        for caller in callers:
            q.append((caller, d + 1))


def handle_for_in(G: Graph, ast_node, extra):
    obj, value, key, body = G.get_ordered_ast_child_nodes(ast_node)
    handled_obj = handle_node(G, obj, extra)
    # switch scopes
    parent_scope = G.cur_scope
    G.cur_scope = \
        G.add_scope('BLOCK_SCOPE', decl_ast=body,
                    scope_name=G.scope_counter.gets(f'Block{body}'))
    G.scope_stack.append(G.cur_scope)
    has_branches = (len(handled_obj.obj_nodes) > 1)
    for obj in handled_obj.obj_nodes:
        # handle and declare the loop variable
        handled_key = handle_node(G, key, extra)
        if G.finished or G.time_limit_reached:
            break
        # if the object is an array, only use numeric indices
        numeric_only = (G.get_node_attr(obj).get('type') == 'array')
        # loop through object's property names
        # if it's a wildcard object, include "__proto__"
        prop_names = G.get_prop_names(obj,
                        exclude_proto=not is_wildcard_obj(G, obj),
                        numeric_only=numeric_only,
                        exclude_wildcard=True)
        if is_wildcard_obj(G, obj):
            if G.check_proto_pollution:
                # wildcard property for wildcard object
                prop_names = [wildcard]
                logger.debug(f'{obj} is a wildcard object.')
            else:
                # wildcard property for wildcard object
                prop_names.insert(0, wildcard)
                logger.debug(f'{obj} is a wildcard object.')
        for k in prop_names:
            if str(k).startswith('Obj#'): # object-based keys
                key_obj = k[4:]
            else:
                # assign the name to the loop variable as a new 
                # literal object
                key_obj = G.add_obj_node(ast_node=ast_node,
                    js_type='string', value=k)
                add_contributes_to(G, [obj], key_obj)
            logger.debug('For-in loop variables: '
                f'{sty.ef.i}{handled_key.name}{sty.rs.all}: '
                f'{sty.fg.green}{key_obj}{sty.rs.all}: {k} from obj {obj}')
            # text-based for-stack
            # G.for_stack.append('for-in {} {} {} in {}'
            #     .format(node_id, handled_key.name, k, obj))
            # full functional for-stack
            # (type, ast node, scope, loop var name, loop var value,
            #                       loop var value list, loop var origin list)
            G.for_stack.append(('for-in', ast_node, G.cur_scope,
                handled_key.name, k, prop_names, handled_obj.obj_nodes))
            # print(G.for_stack)
            G.assign_obj_nodes_to_name_node(handled_key.name_nodes[0],
                [key_obj], branches=extra.branches)
            # run the body
            G.last_stmts = [ast_node]
            simurun_block(G, body, branches=extra.branches)
            G.for_stack.pop()
        logger.debug('For-in loop {} finished'.format(ast_node))
    # switch back the scope
    G.cur_scope = parent_scope
    G.scope_stack.pop()

def handle_for_in_fast(G: Graph, ast_node, extra):
    def get_key_obj(k):
        nonlocal G, ast_node
        if str(k).startswith('Obj#'): # object-based keys
            key_obj = k[4:]
        else:
            # assign the name to the loop variable as a new 
            # literal object
            key_obj = G.add_obj_node(ast_node=ast_node,
                js_type='string', value=k)
        return key_obj

    obj, value, key, body = G.get_ordered_ast_child_nodes(ast_node)
    handled_obj = handle_node(G, obj, extra)
    # switch scopes
    parent_scope = G.cur_scope
    G.cur_scope = \
        G.add_scope('BLOCK_SCOPE', decl_ast=body,
                    scope_name=G.scope_counter.gets(f'Block{body}'))
    G.scope_stack.append(G.cur_scope)
    # handle and declare the loop variable
    handled_key = handle_node(G, key, extra)
    if G.finished or G.time_limit_reached:
        return
    keys = set()
    key_objs = []
    for obj in handled_obj.obj_nodes:
        # if the object is an array, only use numeric indices
        numeric_only = (G.get_node_attr(obj).get('type') == 'array')
        # loop through object's property names
        # if it's a wildcard object, include "__proto__"
        prop_names = G.get_prop_names(obj,
                        exclude_proto=not is_wildcard_obj(G, obj),
                        numeric_only=numeric_only,
                        exclude_wildcard=False)
        keys.update(prop_names)
    key_objs = list(map(get_key_obj, keys))
    G.assign_obj_nodes_to_name_node(handled_key.name_nodes[0],
        key_objs, branches=extra.branches)
    # run the body
    G.last_stmts = [ast_node]
    simurun_block(G, body, branches=extra.branches)
    # switch back the scope
    G.cur_scope = parent_scope
    G.scope_stack.pop()

def handle_for_of(G: Graph, ast_node, extra):
    obj, value, key, body = G.get_ordered_ast_child_nodes(ast_node)
    handled_obj = handle_node(G, obj, extra)
    # switch scopes
    parent_scope = G.cur_scope
    G.cur_scope = \
        G.add_scope('BLOCK_SCOPE', decl_ast=body,
                    scope_name=G.scope_counter.gets(f'Block{body}'))
    G.scope_stack.append(G.cur_scope)
    has_branches = (len(handled_obj.obj_nodes) > 1)
    for obj in handled_obj.obj_nodes:
        # handle and declare the loop variable
        handled_value = handle_node(G, value, extra)
        if G.finished or G.time_limit_reached:
            break
        # if the object is an array, only use numeric indices
        numeric_only = (G.get_node_attr(obj).get('type') == 'array')
        # loop through object's property name nodes
        # if it's a wildcard object, include "__proto__"
        prop_name_nodes = G.get_prop_name_nodes(obj,
                                exclude_proto=not is_wildcard_obj(G, obj),
                                numeric_only=numeric_only,
                                exclude_wildcard=True)
        if is_wildcard_obj(G, obj):
            # wildcard property for wildcard object
            wildcard_prop_name_node = G.get_prop_name_node(wildcard, obj)
            wildcard_prop_obj_nodes = G.get_obj_nodes(
                wildcard_prop_name_node, branches=extra.branches)
            if not wildcard_prop_obj_nodes or not wildcard_prop_obj_nodes:
                wildcard_prop_obj_nodes = [G.add_obj_as_prop(wildcard,
                    ast_node, value=wildcard, parent_obj=obj)]
                wildcard_prop_name_node = G.get_prop_name_node(wildcard, obj)
            prop_name_nodes.insert(0, wildcard_prop_name_node)
            logger.debug(f'{obj} is a wildcard object.')
        prop_obj_nodes = list(map(lambda nn:
            G.get_obj_nodes(nn, branches=extra.branches), prop_name_nodes))
        for name_node, obj_nodes in zip(prop_name_nodes, prop_obj_nodes):
            # obj_nodes = G.get_obj_nodes(name_node, branches=extra.branches)
            k = G.get_node_attr(name_node).get('name')
            logger.debug('For-of loop variables: '
                f'{sty.ef.i}{handled_value.name}{sty.rs.all}: '
                f'{sty.fg.green}{k}{sty.rs.all}: {obj_nodes} from obj {obj}')
            # text-based for-stack
            # ----------------------------------------------------------
            # full functional for-stack
            # (type, ast node, scope, loop var name, loop var value,
            #                       loop var value list, loop var origin list)
            G.for_stack.append(('for-of', ast_node, G.cur_scope,
                handled_value.name, obj_nodes,
                prop_obj_nodes, handled_obj.obj_nodes))
            # print(G.for_stack)
            G.assign_obj_nodes_to_name_node(handled_value.name_nodes[0],
                obj_nodes, branches=extra.branches)
            # run the body
            G.last_stmts = [ast_node]
            simurun_block(G, body, branches=extra.branches)
            G.for_stack.pop()
        logger.debug('For-of loop {} finished'.format(ast_node))
    # switch back the scope
    G.cur_scope = parent_scope
    G.scope_stack.pop()

def handle_for_of_fast(G: Graph, ast_node, extra):
    obj, value, key, body = G.get_ordered_ast_child_nodes(ast_node)
    handled_obj = handle_node(G, obj, extra)
    # switch scopes
    parent_scope = G.cur_scope
    G.cur_scope = \
        G.add_scope('BLOCK_SCOPE', decl_ast=body,
                    scope_name=G.scope_counter.gets(f'Block{body}'))
    G.scope_stack.append(G.cur_scope)
    # handle and declare the loop variable
    handled_value = handle_node(G, value, extra)
    if G.finished or G.time_limit_reached:
        return
    prop_objs = set()
    for obj in handled_obj.obj_nodes:
        # if the object is an array, only use numeric indices
        numeric_only = (G.get_node_attr(obj).get('type') == 'array')
        # loop through object's property name nodes
        # if it's a wildcard object, include "__proto__"
        prop_obj_nodes = G.get_prop_obj_nodes(obj,
                                exclude_proto=not is_wildcard_obj(G, obj),
                                numeric_only=numeric_only)
        prop_objs.update(prop_obj_nodes)
    G.assign_obj_nodes_to_name_node(handled_value.name_nodes[0],
        prop_objs, branches=extra.branches)
    # run the body
    G.last_stmts = [ast_node]
    simurun_block(G, body, branches=extra.branches)
    # switch back the scope
    G.cur_scope = parent_scope
    G.scope_stack.pop()

def handle_for_of_legacy(G: Graph, ast_node, extra):
    obj, value, key, body = G.get_ordered_ast_child_nodes(ast_node)
    handled_obj = handle_node(G, obj, extra)
    # switch scopes
    parent_scope = G.cur_scope
    G.cur_scope = \
        G.add_scope('BLOCK_SCOPE', decl_ast=body,
                    scope_name=G.scope_counter.gets(f'Block{body}'))
    G.scope_stack.append(G.cur_scope)
    has_branches = (len(handled_obj.obj_nodes) > 1)
    # print(sty.fg.li_green, handled_obj.obj_nodes, sty.rs.all)
    for obj in handled_obj.obj_nodes:
        # handle and declare the loop variable
        handled_value = handle_node(G, value, extra)
        if G.finished or G.time_limit_reached:
            break
        # if the object is an array, only use numeric indices
        numeric_only = (G.get_node_attr(obj).get('type') == 'array')
        # loop through object's property object nodes
        # if it's a wildcard object, include its prototype
        prop_obj_nodes = G.get_prop_obj_nodes(obj,
            branches=extra.branches, numeric_only=numeric_only,
            exclude_proto=not is_wildcard_obj(G, obj))
        if is_wildcard_obj(G, obj):
            # wildcard property for wildcard object
            wildcard_prop_obj_nodes = G.get_prop_obj_nodes(obj,
                prop_name=wildcard, branches=extra.branches)
            if not wildcard_prop_obj_nodes:
                wildcard_prop_obj_nodes = [G.add_obj_as_prop(wildcard,
                    ast_node, value=wildcard, parent_obj=obj)]
            prop_obj_nodes.extend(wildcard_prop_obj_nodes)
            prop_obj_nodes = list(set(prop_obj_nodes))
            logger.debug(f'{obj} is a wildcard object.')
        # for v in prop_obj_nodes:
        #     G.for_stack.append('for-of {} {} {}'.format(node_id, v,
        #         G.get_node_attr(v).get("code")))
        #     print(G.for_stack)
        #     # assign the object node to the loop variable
        #     logger.debug('For-of loop variables: '
        #         f'{sty.ef.i}{handled_value.name}{sty.rs.all}: '
        #         f'{sty.fg.green}{v}{sty.rs.all}: {G.get_node_attr(v).get("code")}'
        #         f' from obj {obj}')
        #     G.assign_obj_nodes_to_name_node(handled_value.name_nodes[0],
        #         [v], branches=extra.branches)
        #     # run the body
        #     simurun_block(G, body, branches=extra.branches)
        #     G.for_stack.pop()

        # text-based for-stack
        # G.for_stack.append('for-of {} {} {}'.format(ast_node, prop_obj_nodes,
        #     [G.get_node_attr(v).get("code") for v in prop_obj_nodes]))
        # full functional for-stack
        # (ast node, scope, loop var name, loop var, loop var list, loop var origin list)
        G.for_stack.append(('for-of', ast_node, G.cur_scope, None, [] # TODO
            , handled_obj.obj_nodes))
        # print(G.for_stack)
        # assign the object node to the loop variable
        G.assign_obj_nodes_to_name_node(handled_value.name_nodes[0],
            prop_obj_nodes, branches=extra.branches)
        # run the body
        G.last_stmts = [ast_node]
        simurun_block(G, body, branches=extra.branches)
        G.for_stack.pop()
        logger.debug('For-of loop {} finished'.format(ast_node))
    # switch back the scope
    G.cur_scope = parent_scope
    G.scope_stack.pop()

def handle_class(G: Graph, ast_node, extra):
    children = G.get_ordered_ast_child_nodes(ast_node)
    name = G.get_node_attr(children[0]).get('code')
    class_obj = G.add_obj_node(ast_node=None, js_type='function')
    G.set_node_attr(class_obj, ('name', name))
    G.set_node_attr(class_obj, ('value', f'[class {name}]'))
    # print(ast_node, G.get_node_attr(ast_node), children)
    toplevel = children[4]
    body = G.get_child_nodes(toplevel, edge_type='PARENT_OF',
                             child_type='AST_STMT_LIST')[0]
    prev_dont_quit = G.dont_quit
    G.dont_quit = 'class'
    simurun_class_body(G, body, ExtraInfo(extra, class_obj=class_obj))
    G.dont_quit = prev_dont_quit
    if G.get_obj_def_ast_node(class_obj) is None:
        ast = G.add_blank_func(name)
        G.add_edge(class_obj, ast, {'type:TYPE': 'OBJ_TO_AST'})
    if G.find_nearest_upper_CPG_node(ast_node) == ast_node:
        G.add_obj_to_scope(name, tobe_added_obj=class_obj)
    return NodeHandleResult(obj_nodes=[class_obj])
    
def handle_method(G: Graph, ast_node, extra):
    assert extra.class_obj is not None
    name = G.get_name_from_child(ast_node)
    if name == 'constructor':
        G.add_edge(extra.class_obj, ast_node, {'type:TYPE': 'OBJ_TO_AST'})
    else:
        method_obj = decl_function(G, ast_node, add_to_scope=False)
        prototypes = G.get_prop_obj_nodes(extra.class_obj, 'prototype', 
                                          branches=extra.branches)
        for p in prototypes:
            G.add_obj_as_prop(name, parent_obj=p, tobe_added_obj=method_obj)

def simurun_class_body(G, ast_node, extra):
    """
    Simurun the body of a class
    """
    if extra is None or extra.branches is None:
        branches = BranchTagContainer()
    else:
        branches = extra.branches

    logger.log(ATTENTION, 'BLOCK {} STARTS, SCOPE {}'.format(ast_node, G.cur_scope))
    stmts = G.get_ordered_ast_child_nodes(ast_node)
    # control flows
    for last_stmt in G.last_stmts:
        G.add_edge_if_not_exist(last_stmt, ast_node, {'type:TYPE': 'FLOWS_TO'})
    G.last_stmts = [ast_node]
    # simulate statements
    for stmt in stmts:

        # build control flows from the previous statement to the current one
        for last_stmt in G.last_stmts:
            G.add_edge_if_not_exist(last_stmt, stmt, {'type:TYPE': 'FLOWS_TO'})
        G.last_stmts = [stmt]
        G.cur_stmt = stmt
        handle_node(G, stmt, ExtraInfo(extra, branches=branches))

        if G.finished or G.time_limit_reached:
            break

        if G.get_node_attr(stmt).get('type') == 'AST_RETURN':
            G.last_stmts = []

def cfg_traverse(G: Graph, current, extra=ExtraInfo()):
    cur_type = G.get_node_attr(current).get('type')
    if cur_type == 'CFG_FUNC_ENTRY':
        pass
    elif cur_type == 'AST_STMT_LIST':
        simurun_block_init(G, current, branches=extra.branches)
    elif cur_type == 'CFG_BLOCK_EXIT':
        simurun_block_finalize(G, current, branches=extra.branches)
    else:
        result = handle_node(G, current, extra)
    G.last_stmts = [current]
    next_nodes = []
    inf = float('inf')
    for e in G.get_out_edges(current, edge_type="FLOWS_TO"):
        next_nodes.append((G.get_node_attr(e[1]).get('local_dist', inf), e[1]))
    next_nodes.sort()
    print('Current:', current, cur_type, 'Next nodes:', next_nodes)
    for dist, next_node in next_nodes:
        cfg_traverse(G, next_node, extra)

def simurun_block_init(G, ast_node, parent_scope=None, branches=None,
    block_scope=True, decl_var=False):
    """
    Simurun a block by running its statements one by one.
    A block is a BlockStatement in JavaScript,
    or an AST_STMT_LIST in PHP.
    """
    if branches is None or G.single_branch:
        branches = BranchTagContainer()

    if parent_scope == None:
        parent_scope = G.cur_scope
    if block_scope:
        G.cur_scope = \
            G.add_scope('BLOCK_SCOPE', decl_ast=ast_node,
                        scope_name=G.scope_counter.gets(f'Block{ast_node}'))
    G.scope_stack.append(G.cur_scope)
    logger.log(ATTENTION, 'BLOCK {} STARTS, SCOPE {}'.format(ast_node, G.cur_scope))
    decl_vars_and_funcs(G, ast_node, var=decl_var)

def simurun_block_finalize(G, ast_node=None, parent_scope=None, branches=None,
    block_scope=True, decl_var=False):
    G.cur_scope = G.scope_stack.pop()

def empty_rough_stacks(G, reason=None):
    logger.info(sty.fg.magenta + sty.ef.inverse + 'Start to empty stack1 {} and stack2 {}'.format(len(G.stack1), len(G.stack2)) + sty.rs.all)
    cur_file_path = G.file_stack[-1] if G.file_stack else None
    G.finished = False
    while True:
        if G.finished:
            break
        while True:
            if G.finished:
                break
            if G.stack2:
                s2i = G.stack2.pop()
                func_obj2 = s2i[0]
                func_name2 = s2i[1]
                _args = s2i[3]
                _this = s2i[4]
                if s2i[5] is not None and cur_file_path is not None and s2i[5] != cur_file_path:
                    G.stack2.append(s2i) # push the tuple back to the stack
                    # log output
                    all_cleared = True
                    for i in G.stack2:
                        if i[5] == cur_file_path:
                            all_cleared = False
                            break
                    logger.debug(sty.fg.magenta + 'Break from stack2 {}\nCurrent file path {}\nAll cleared {}'.format(G.stack2, cur_file_path, all_cleared) + sty.rs.all)
                    break
                G.cur_func_call = s2i
                # logger.info('Stack 2 goes to {} reason {}'.format(s2i, reason))
                call_func_obj(G, func_obj2, _args, _this,
                    func_name=func_name2, is_new=True, dont_skip=True)
                G.finished = False
            else:
                break
        if G.stack1:
            s1i = G.stack1.pop()
            func_obj1 = s1i[0]
            func_name1 = s1i[1]
            _args = s1i[3]
            _this = s1i[4]
            if s1i[5] is not None and cur_file_path is not None and s1i[5] != cur_file_path:
                G.stack1.append(s1i[:6] + (3,)) # push the tuple back to the stack
                # log output
                all_cleared = True
                for i in G.stack1:
                    if i[5] == cur_file_path:
                        all_cleared = False
                        break
                logger.debug(sty.fg.magenta + 'Break from stack1 {}\nCurrent file path {}\nAll cleared {}'.format(G.stack1, cur_file_path, all_cleared) + sty.rs.all)
                empty_task_queues(G)
                break
            G.cur_func_call = s1i
            # logger.info('Stack 1 goes to {} reason {}'.format(s1i, reason))
            call_func_obj(G, func_obj1, _args, _this,
                func_name=func_name1, is_new=True, dont_skip=True)
            G.finished = False
        empty_task_queues(G)
        if not G.stack1: break

def empty_task_queues(G):
    while True:
        if G.task_queue:
            # print('task queue', '|' * len(G.task_queue))
            func1 = G.task_queue.popleft()
            func1(func1, G)
        while True: # always check the micro task queue
            if G.microtask_queue:
                # print('microtask queue', '|' * len(G.microtask_queue))
                func2 = G.microtask_queue.popleft()
                func2(func2, G)
            else:
                break
        if not G.task_queue: break

def python_eval(G: Graph, caller_ast, extra, _, string=NodeHandleResult()):
    input_values = to_values(G, string)[0]
    return_values = []
    for value in input_values:
        return_values.append(eval(value))
    return NodeHandleResult(values=return_values)