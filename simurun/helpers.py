from .graph import Graph
from .utilities import NodeHandleResult, ExtraInfo, BranchTag
from .utilities import wildcard, undefined
from .utilities import get_random_hex
import math
from typing import Callable, List, Iterable
from collections import defaultdict

def eval_value(G: Graph, s: str, return_obj_node=False, ast_node=None):
    '''
    Experimental. Extract Python values, JavaScript types from literal
    values (presented by JavaScript code) and create object nodes.
    
    Args:
        G (Graph): Graph.
        s (str): The literal value (as JavaScript code).
        return_obj_node (bool, optional): Create/return an object node
            for the value. Defaults to False.
        ast_node (optional): The value's AST node. Defaults to None.
    
    Returns:
        evaluated, js_type, result: the Python value, JavaScript type
            (in string), and object node (optional).
    '''
    js_type = None
    result = None
    if s == 'true':
        evaluated = True
        js_type = 'boolean'
        result = NodeHandleResult(name='true', obj_nodes=[G.true_obj])
    elif s == 'false':
        evaluated = False
        js_type = 'boolean'
        result = NodeHandleResult(name='false', obj_nodes=[G.false_obj])
    elif s == 'NaN':
        evaluated = math.nan
        js_type = 'number'
        result = NodeHandleResult(name='NaN', obj_nodes=[G.false_obj])
    elif s == 'Infinity':
        evaluated = math.inf
        js_type = 'number'
        result = NodeHandleResult(name='Infinity', obj_nodes=[G.infinity_obj])
    elif s == '-Infinity':
        evaluated = -math.inf
        js_type = 'number'
        result = NodeHandleResult(name='-Infinity', obj_nodes=[
            G.negative_infinity_obj])
    else:
        evaluated = eval(s)
        if type(evaluated) is float or type(evaluated) is int:
            js_type = 'number'
        elif type(evaluated) is str:
            js_type = 'string'
        if return_obj_node:
            added_obj = G.add_obj_node(ast_node, js_type, s)
            result = NodeHandleResult(obj_nodes=[added_obj])
    if return_obj_node:
        return evaluated, js_type, result
    else:
        return evaluated, js_type

def val_to_str(value, default=wildcard):
    if type(value) in [float, int]:
        return '%g' % value
    else:
        if value is None or value == wildcard:
            return default
        return str(value)

def val_to_float(value, default=wildcard):
    if value is None or value == wildcard or value == undefined:
        return default
    try:
        return float(value)
    except ValueError:
        return float('nan')

def cmp(a, b):
    return (a > b) - (a < b)

def js_cmp(v1, v2):
    if type(v1) == type(v2):
        if v1 == undefined and v2 == undefined:
            return 0
        else:
            return cmp(v1, v2)
    else:
        # s1 = val_to_str(v1)
        # s2 = val_to_str(v2)
        n1 = val_to_float(v1)
        n2 = val_to_float(v2)
        return cmp(n1, n2)

def is_int(x):
    try: # check if x is an integer
        _ = int(x)
    except (ValueError, TypeError):
        return False
    return True

def convert_prop_names_to_wildcard(G: Graph, obj, exclude_length=False,
    exclude_proto=True):
    wildcard_name_node = G.add_prop_name_node(wildcard, obj)
    for e1 in G.get_out_edges(obj, edge_type='OBJ_TO_PROP'):
        name_node = e1[1]
        if G.get_node_attr(name_node).get('name') == wildcard:
            continue
        if exclude_length and \
            G.get_node_attr(name_node).get('name') == 'length':
            continue
        if exclude_proto and \
            G.get_node_attr(name_node).get('name') == '__proto__':
            continue
        for e2 in G.get_out_edges(name_node, edge_type='NAME_TO_OBJ'):
            _, obj, _, data = e2
            G.add_edge(wildcard_name_node, obj, data)
        G.remove_all_edges_between(e1[0], e1[1])    

def copy_objs_for_branch(G: Graph, handle_result: NodeHandleResult, branch,
    ast_node=None, deep=True) -> NodeHandleResult:
    returned_objs = list()
    for obj in handle_result.obj_nodes:
        copied_obj = None
        for e in G.get_in_edges(obj, edge_type='NAME_TO_OBJ'):
            name_node, _, _, data = e
            eb = data.get('branch')
            if name_node in handle_result.name_nodes and (eb is None or
                (eb.point == branch.point and eb.branch != branch.branch)):
                if copied_obj is None: # the object should be copied only once
                    copied_obj = G.copy_obj(obj, ast_node, deep=deep)
                    returned_objs.append(copied_obj)
                # assign the name node to the copied object and mark the
                # previous edge as deleted (D)
                edge_attr_a = dict(data)
                edge_attr_a['branch'] = BranchTag(branch, mark='A')
                edge_attr_d = dict(data)
                edge_attr_d['branch'] = BranchTag(branch, mark='D')
                G.add_edge(name_node, copied_obj, edge_attr_a)
                G.add_edge(name_node, obj, edge_attr_d)
        if copied_obj is None: # if the object is not copied, return it
            returned_objs.append(obj)

    return NodeHandleResult(obj_nodes=returned_objs, name=handle_result.name,
        name_node=handle_result.name_nodes)

def copy_objs_for_parameters(G: Graph, handle_result: NodeHandleResult,
    ast_node=None, number_of_copies=1, delete_original=True) -> List[List]:
    # deprecated
    returned_objs = list()
    for obj in handle_result.obj_nodes:
        copied_objs = []
        for i in range(number_of_copies):
            copied_objs.append(G.copy_obj(obj, ast_node))
        for e in G.get_in_edges(obj, edge_type='NAME_TO_OBJ'):
            name_node, obj_node, k, data = e
            if name_node in handle_result.name_nodes:
                if delete_original:
                    G.graph.remove_edge(name_node, obj_node, k)
                for copied_obj in copied_objs:
                    G.add_edge(name_node, copied_obj, data)
        returned_objs.append(copied_objs)

    return returned_objs

def to_python_array(G: Graph, array_obj, value=False):
    elements = [[]]
    edge_data = [[]]
    for name_node in G.get_prop_name_nodes(array_obj):
        name = G.get_node_attr(name_node).get('name')
        if name == 'length' or name == '__proto__':
            continue
        try:
            i = int(name)
            if i < 0: # what the fuck??
                continue
            while i >= len(elements):
                elements.append([])
                edge_data.append([])
        except (ValueError, TypeError):
            continue
        for e in G.get_out_edges(name_node, edge_type='NAME_TO_OBJ'):
            if value:
                elements[i].append(val_to_str(G.get_node_attr(e[1])
                    .get('code')))
            else:
                elements[i].append(e[1])
            edge_data[i].append(e[3])
    return elements, edge_data

def to_og_array(G: Graph, elements, edge_data, ast_node=None):
    added_array = G.add_obj_node(ast_node=ast_node, js_type='array')
    for i, elem in enumerate(elements):
        name_node = G.add_prop_name_node(name=str(i), parent_obj=added_array)
        for j, obj in enumerate(elem):
            G.add_edge(name_node, obj,
                {'type:TYPE': 'NAME_TO_OBJ', **edge_data[i][j]})
    G.add_obj_as_prop(prop_name='length', ast_node=ast_node, js_type='number',
        value=len(elements), parent_obj=added_array)
    return added_array

# def add_contributes_to(G: Graph, sources: Iterable, target,
#     chain_tainted=True):
#     '''
#     DO NOT USE THIS VERSION!
#     '''
#     assert not isinstance(sources, (str, bytes))
#     tainted = False
#     for s in sources:
#         # source_id = str(s)
#         # if G.get_node_attr(s).get('tainted'):
#         #     source_id += ' tainted'
#         # print(f'{source_id} CONTRIBUTES TO {target}')
#         G.add_edge(s, target, {'type:TYPE': 'CONTRIBUTES_TO'})
#         tainted = tainted or G.get_node_attr(s).get('tainted', False)
#     if chain_tainted and tainted:
#         G.set_node_attr(target, ('tainted', True))

def is_wildcard_obj(G, obj):
    attrs = G.get_node_attr(obj)
    return ((attrs.get('type') in ['object', 'array'] and
            attrs.get('code') == wildcard)
        or (attrs.get('type') in ['number', 'string'] and
            attrs.get('code')== wildcard)
        or attrs.get('type') == wildcard)

def get_func_name(G: Graph, ast_node, recursive=True):
    '''
    Get the called function name (for call expression) or function
    name (for function declaration). If the callee is a method of an
    object, it returns the method name only instead of
    parent.method.
    '''
    node_type = G.get_node_attr(ast_node).get('type')
    if node_type in ['AST_FUNC_DECL', 'AST_CLOSURE', 'AST_STMT_LIST']:
        name = G.get_name_from_child(ast_node, max_depth=2)
        if not name or name == '{closure}':
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
                'AST_CLOSURE']:
                return get_func_name(G, left)
    else:
        return G.get_name_from_child(ast_node)