from .trace_rule import TraceRule
from .vul_func_lists import *

def get_path_text(G, path, caller):
    """
    get the code by ast number
    Args:
        G: the graph
        path: the path with ast nodes
    Return:
        str: a string with text path
    """
    res_path = ""
    cur_path_str1 = ""
    cur_path_str2 = ""
    for node in path:
        cur_node_attr = G.get_node_attr(node)
        if cur_node_attr.get('lineno:int') is None:
            continue
        if cur_node_attr.get('labels:label') in ['Artificial', 'Artificial_AST']:
            continue
        # if cur_node_attr.get('lineno:int') == '': # workaround?
        #     G.logger.error('No line number for node {} {}'.format(node, cur_node_attr))
        #     continue
        cur_path_str1 += cur_node_attr['lineno:int'] + '->'
        start_lineno = int(cur_node_attr['lineno:int'])
        end_lineno = int(cur_node_attr['endlineno:int']
                        or start_lineno)
        content = None
        try:
            content = G.get_node_file_content(node)
        except:
            pass
        if content is not None:
            cur_path_str2 += "{}\t{}".format(start_lineno,
                    ''.join(content[start_lineno:end_lineno + 1]))
    cur_path_str1 += G.get_node_attr(caller).get('lineno:int', '?')
    G.logger.debug(cur_path_str1)

    res_path += "==========================\n"
    res_path += "{}\n".format(G.get_node_file_path(path[0]))
    res_path += cur_path_str2
    return res_path

def traceback(G, vul_type, start_node=None):
    """
    traceback from the leak point, the edge is OBJ_REACHES
    Args:
        G: the graph
        vul_type: the type of vulernability, listed below

    Return:
        the paths include the objs,
        the string description of paths,
        the list of callers,
    """
    def find_func_name(node):
        func = G.get_node_attr(node).get('funcid:int')
        if not func:
            while G.get_node_attr(node).get('type') not in [
                'AST_FUNC_DECL', 'AST_CLOSURE', 'AST_METHOD', 'AST_TOPLEVEL']:
                node = G.get_in_edges(node, edge_type='PARENT_OF')[0][0]
            func = node
        # print('found node', node, 'in function', func, G.get_name_from_child(func))
        return G.get_name_from_child(func)
    res_path = ""
    expoit_func_list = signature_lists[vul_type]

    if G.new_trace_rule:
        func_nodes = G.get_node_by_attr('type', 'DUMMY_STMT')
        # print('func nodes', func_nodes)
    else:
        func_nodes = G.get_node_by_attr('type', 'AST_METHOD_CALL')
        func_nodes += G.get_node_by_attr('type', 'AST_CALL')
        func_nodes += G.get_node_by_attr('type', 'AST_NEW')
    ret_pathes = []
    caller_list = []
    for func_node in func_nodes:
        # we assume only one obj_decl edge
        if G.new_trace_rule:
            func_name = find_func_name(func_node)
        else:
            func_name = G.get_name_from_child(func_node, order=1)
        # print('trace back func name', func_name, 'type', G.get_node_attr(func_node).get('type'))
        if func_name in expoit_func_list:
            caller = func_node
            caller = G.find_nearest_upper_CPG_node(caller)
            caller_list.append("{} called {}".format(caller, func_name))
            pathes = G._dfs_upper_by_edge_type(caller, "OBJ_REACHES")

            # here we treat the single calling as a possible path
            # pathes.append([caller])
            G.logger.debug('Paths:')

            # give the end node one more chance, find the parent obj of the ending point
            """
            for path in pathes:
                last_node = path[-1]
                upper_nodes = G._dfs_upper_by_edge_type(last_node, 
                        "OBJ_TO_PROP")
                for uppernode in upper_nodes:
                    path.append(uppernode)
                #print('--', upper_nodes)
            """
            for path in pathes:
                ret_pathes.append(path)
                path.reverse()
                res_path += get_path_text(G, path, caller)
    return ret_pathes, res_path, caller_list

def do_vul_checking(G, rule_list, pathes):
    """
    checking the vuleralbilities in the pathes

    Args:
        G: the graph object
        rule_list: a list of paires, (rule_function, args of rule_functions)
        pathes: the possible pathes
    Returns:
        
    """
    trace_rules = []
    for rule in rule_list:
        trace_rules.append(TraceRule(rule[0], rule[1], G))

    success_pathes = []
    flag = True
    for path in pathes:
        flag = True
        for trace_rule in trace_rules:
            # print('path =', path)
            if not trace_rule.check(path):
                flag = False
                break
        if flag:
            success_pathes.append(path)
    return success_pathes

def vul_checking(G, pathes, vul_type):
    """
    picking the pathes which satisfy the xss
    Args:
        G: the Graph
        pathes: the possible pathes
    return:
        a list of xss pathes
    """
    xss_rule_lists = [
            [('has_user_input', None), ('not_start_with_func', ['sink_hqbpillvul_http_write']), ('not_exist_func', ['parseInt']), ('end_with_func', ['sink_hqbpillvul_http_write'])],
            [('has_user_input', None), ('not_start_with_func', ['sink_hqbpillvul_http_setHeader']), ('not_exist_func', ['parseInt']), ('end_with_func', ['sink_hqbpillvul_http_setHeader'])]
            ]
    os_command_rule_lists = [
            [('has_user_input', None), ('not_start_within_file', ['child_process.js']), ('not_exist_func', ['parseInt'])]
            ]

    code_exec_lists = [
            [('has_user_input', None), ('not_start_within_file', ['eval.js']), ('not_exist_func', ['parseInt'])],
            [('has_user_input', None), ('end_with_func', ['Function']), ('not_exist_func', ['parseInt'])],
            [('has_user_input', None), ('end_with_func', ['eval']), ('not_exist_func', ['parseInt'])],
            # include os command here
            [('has_user_input', None), ('not_start_within_file', ['child_process.js']), ('not_exist_func', ['parseInt'])]
            ]
    proto_pollution = [
            [('has_user_input', None), ('not_exist_func', signature_lists['sanitation'])]
            ]
    path_traversal = [
            [('start_with_var', ['OPGen_TAINTED_VAR_url']),
                ('not_exist_func', signature_lists['sanitation']), 
                ('end_with_func', signature_lists['path_traversal']),
                ('exist_func', ['sink_hqbpillvul_fs_read'])
                # ('exist_func', ['__opgCombine'])
            ],
            [('start_with_var', ['OPGen_TAINTED_VAR_url']),
                ('not_exist_func', ['parseInt']), 
                ('end_with_func', ['sink_hqbpillvul_http_sendFile'])
            ]
            ]
    nosql_rule_lists = [
            [('has_user_input', None), ('not_start_within_file', ['mongodb.js', 'monk.js']), ('not_exist_func', ['parseInt'])]
            ]

    vul_type_map = {
            "xss": xss_rule_lists,
            "os_command": os_command_rule_lists,
            "code_exec": code_exec_lists,
            "proto_pollution": proto_pollution,
            "path_traversal": path_traversal,
            "nosql": nosql_rule_lists
            }

    rule_lists = vul_type_map[vul_type]
    success_pathes = []
    print('vul_checking', vul_type)
    """
    print(pathes)
    for path in pathes:
        for node in path:
            print(G.get_node_attr(node))
    """
    for rule_list in rule_lists:
        success_pathes += do_vul_checking(G, rule_list, pathes)
    print("success: ", success_pathes)
    return success_pathes

def check_pp(G):
    print('Checking proto_pollution...')
    def _get_children(node_id, edge_type=None, child_type=None, child_label=None, edge_scope=None):
        nonlocal G
        children, scopes = [], []
        edges = G.get_out_edges(node_id, edge_type=edge_type)
        for edge in edges:
            aim_node_attr = G.get_node_attr(edge[1])
            aim_edge_scope = edge[-1].get('scope')
            if child_type is not None and aim_node_attr.get('type') != child_type:
                continue
            if child_label is not None and aim_node_attr.get('labels:label') != child_label:
                continue
            if edge_scope is not None and aim_edge_scope != edge_scope:
                continue
            children.append(edge[1])
            scopes.append(aim_edge_scope)
        return children, scopes

    results = set()
    for node in G.get_all_nodes():
        # check every assignment
        if G.get_node_attr(node).get('type') != 'AST_ASSIGN':
            continue
        children = G.get_ordered_ast_child_nodes(node)
        if len(children) != 2:
            continue
        left, right = children
        # whose left side is prop expression
        if G.get_node_attr(left).get('type') not in ['AST_DIM', 'AST_PROP']:
            continue
        # get all possible scopes
        _, scopes = _get_children(left, edge_type='REFERS_TO', child_label='Name')
        for scope in set(scopes):
            # the left side should have the name nodes of functions in built-in prototypes
            name_nodes, _ = _get_children(left, edge_type='REFERS_TO', child_label='Name', edge_scope=scope)
            if not (set(name_nodes) & set(G.pollutable_name_nodes)):
                continue
            # make sure the property names are tainted
            prop_children = G.get_ordered_ast_child_nodes(left)
            if len(prop_children) != 2:
                continue
            prop_name_ast_node = prop_children[1]
            prop_name_obj_nodes, _ = _get_children(prop_name_ast_node, edge_type='REFERS_TO', child_label='Object', edge_scope=scope)
            if not any(map(lambda obj: G.get_node_attr(obj).get('tainted'), prop_name_obj_nodes)):
                continue
            # the right side should have tainted objects
            obj_nodes, _ = _get_children(right, edge_type='REFERS_TO', child_label='Object', edge_scope=scope)
            if not any(map(lambda obj: G.get_node_attr(obj).get('tainted'), obj_nodes)):
                continue
            # if found, add the AST node
            results.add(node)
    if results:
        print('found:', results)
    else:
        print('not found')
    return results
