class TraceRuleInterface:
    def __init__(self, key, value, G):
        pass

    def check(self, path):
        pass
    

class TraceRuleNew(TraceRuleInterface):
    """
    a rule container, which include a rule and a related checking function
    """

    def __init__(self, key, value, G):
        self.key = key
        self.value = value
        self.graph = G

    def find_func_name(self, node):
        func = self.graph.get_node_attr(node).get('funcid:int')
        if not func:
            while True:
                print('goes to', node, self.graph.get_node_attr(node), self.graph.get_in_edges(node, edge_type='PARENT_OF'))
                if self.graph.get_node_attr(node).get('type') in [
                        'AST_FUNC_DECL', 'AST_CLOSURE', 'AST_METHOD', 'AST_TOPLEVEL']:
                    func = node
                    break
                edges = self.graph.get_in_edges(node, edge_type='PARENT_OF')
                if edges:
                    node = self.graph.get_in_edges(node, edge_type='PARENT_OF')[0][0]
                else:
                    func = None
                    break
        # print('found node', node, 'in function', func, self.graph.get_name_from_child(func))
        return self.graph.get_name_from_child(func) if func is not None else None

    def exist_func(self, func_names, path):
        """
        check whether in the path, all functions within {func_names} exists

        Args:
            func_names: a list of function names that need to appear in the path
            path: the path need to be checked

        Returns:
            checking result
        """
        called_func_list = set()
        for node in path:
            called_func_list.add(self.find_func_name(node))

        # print("@@@@@@@@ CALLED FUNCTIONS", called_func_list)

        for called_func_name in called_func_list:
            if called_func_name in func_names:
                return True

        return False 

    def not_exist_func(self, func_names, path):
        """
        check if there exist a function named func_names in the path
        """
        return not self.exist_func(func_names, path)

    def start_with_func(self, func_names, path):
        """
        check whether a path starts with a function

        Args:
            func_names: the possible function names
            path: the path needed to be checked
        Return:
            True or False
        """
        start_node = path[0]
        cur_func = self.find_func_name(start_node)
        return cur_func in func_names 

    def not_start_with_func(self, func_names, path):
        """
        check whether a path starts with a function

        Args:
            func_names: the possible function names
            path: the path needed to be checked
        Return:
            True or False
        """
        return not self.start_with_func(func_names, path)

    def not_start_within_file(self, file_names, path):
        """
        check whether a path starts within a file
        Args:
            file_names: the possible file names
            path: the path to be checked
        Return:
            True or False
        """
        start_node = path[0]
        return not self.start_within_file(file_names, path)

    def end_with_func(self, func_names, path):
        """
        check whether a path ends with a function

        Args:
            func_names: the possible function names
            path: the path needed to be checked
        Return:
            True or False
        """
        end_node = path[-1]
        cur_func = self.find_func_name(end_node)
        return cur_func in func_names

    def start_within_file(self, file_names, path):
        """
        check whether a path starts within a file
        Args:
            file_names: the possible file names
            path: the path to be checked
        Return:
            True or False
        """
        start_node = path[0]

        file_name = self.graph.get_node_file_path(start_node)
        cur_node = self.graph.get_node_attr(start_node)
        if file_name is None:
            return False
        file_name = file_name if '/' not in file_name else file_name.split('/')[-1]
        return file_name in file_names

    def start_with_var(self, var_names, path):
        #TODO: not finished, need to update the var name finding algorithm
        """
        check whether a path starts with a variable 
        Args:
            var_names: the possible var names
            path: the path to be checked
        Return:
            True or False
        """
        start_node = path[0]

        path_start_var_name = self.graph.get_name_from_child(start_node)
        cur_node = self.graph.get_node_attr(start_node)
        if path_start_var_name is None:
            return False
        return path_start_var_name in var_names

    def has_user_input(self, _, path):
        """
        check if any node in this path contains user input
        user input is defined as in the http, process or 
        the arguments of the module entrance functions
        
        we check by the obj in the edges
        Args: 
            path: the path
        Return:
            True or False
        """
        pre_node = None
        for node in path:
            if not pre_node:
                pre_node = node;
                continue
            
            cur_edges = self.graph.get_edge_attr(pre_node, node)
            # print("{} --{}--> {}".format(pre_node, cur_edges, node))
            if not cur_edges:
                continue
            for k in cur_edges:
                if 'type:TYPE' in cur_edges[k] and cur_edges[k]['type:TYPE'] == "OBJ_REACHES":
                    obj = cur_edges[k]['obj']
                    obj_attr = self.graph.get_node_attr(obj)
                    if 'tainted' in obj_attr and obj_attr['tainted']:
                        return True
            pre_node = node

            """
            all_child = self.graph.get_all_child_nodes(node)
            objs = []
            for child in all_child:
                objs += self.graph.get_in_edges(child, edge_type='OBJ_TO_AST')
            for obj in objs:
                node_attr = self.graph.get_node_attr(obj[0])
                # here we only keep the obj which in the OBJ_REACHES edges
                if 'tainted' in node_attr and node_attr['tainted']:
                    print(obj[0], node_attr, self.graph.get_node_attr(obj[1]))
                    return True
            """
        if self.start_within_file(['http.js', 'process.js', 'yargs.js'], path):
            return True
        return False

    def check(self, path):
        """
        select the checking function and run it based on the key value
        Return:
            the running result of the obj
        """
        key_map = {
                "exist_func": self.exist_func,
                "not_exist_func": self.not_exist_func,
                "start_with_func": self.start_with_func,
                "not_start_with_func": self.not_start_with_func,
                "start_within_file": self.start_within_file,
                "not_start_within_file": self.not_start_within_file,
                "end_with_func": self.end_with_func,
                "has_user_input": self.has_user_input,
                "start_with_var": self.start_with_var
                }

        if self.key in key_map:
            check_function = key_map[self.key]
        else:
            return False

        return check_function(self.value, path)


class TraceRuleOld(TraceRuleInterface):
    """
    a rule container, which include a rule and a related checking function
    """

    def __init__(self, key, value, G):
        self.key = key
        self.value = value
        self.graph = G

    def exist_func(self, func_names, path):
        """
        check whether in the path, all functions within {func_names} exists

        Args:
            func_names: a list of function names that need to appear in the path
            path: the path need to be checked

        Returns:
            checking result
        """
        called_func_list = set()
        for node in path:
            childern = self.graph.get_all_child_nodes(node)
            for child in childern:
                cur_node = self.graph.get_node_attr(child)
                if 'type' in cur_node:
                    if cur_node['type'] == 'AST_CALL' or cur_node['type'] == 'AST_METHOD_CALL':
                        cur_func = self.graph.get_name_from_child(child)
                        called_func_list.add(cur_func)

        # print("@@@@@@@@ CALLED FUNCTIONS", called_func_list)

        for called_func_name in called_func_list:
            if called_func_name in func_names:
                return True

        return False 

    def not_exist_func(self, func_names, path):
        """
        check if there exist a function named func_names in the path
        """
        return not self.exist_func(func_names, path)

    def start_with_func(self, func_names, path):
        """
        check whether a path starts with a function

        Args:
            func_names: the possible function names
            path: the path needed to be checked
        Return:
            True or False
        """
        start_node = path[0]

        childern = self.graph.get_all_child_nodes(start_node)
        for child in childern:
            cur_node = self.graph.get_node_attr(child)
            if 'type' in cur_node:
                if cur_node['type'] == 'AST_CALL' or cur_node['type'] == 'AST_METHOD_CALL':
                    cur_func = self.graph.get_name_from_child(child)
                    if cur_func not in func_names:
                        # if not current, maybe inside the call there is another call
                        continue
                    return cur_func in func_names 
        return False

    def not_start_with_func(self, func_names, path):
        """
        check whether a path starts with a function

        Args:
            func_names: the possible function names
            path: the path needed to be checked
        Return:
            True or False
        """
        return not self.start_with_func(func_names, path)

    def not_start_within_file(self, file_names, path):
        """
        check whether a path starts within a file
        Args:
            file_names: the possible file names
            path: the path to be checked
        Return:
            True or False
        """
        start_node = path[0]
        return not self.start_within_file(file_names, path)

    def end_with_func(self, func_names, path):
        """
        check whether a path ends with a function

        Args:
            func_names: the possible function names
            path: the path needed to be checked
        Return:
            True or False
        """
        end_node = path[-1]

        childern = self.graph.get_all_child_nodes(end_node)
        for child in childern:
            cur_node = self.graph.get_node_attr(child)
            if 'type' in cur_node:
                if cur_node['type'] == 'AST_CALL' or cur_node['type'] == 'AST_METHOD_CALL':
                    cur_func = self.graph.get_name_from_child(child)
                    if cur_func not in func_names:
                        # if not current, maybe inside the call there is another call
                        continue
                    return cur_func in func_names 

    def start_within_file(self, file_names, path):
        """
        check whether a path starts within a file
        Args:
            file_names: the possible file names
            path: the path to be checked
        Return:
            True or False
        """
        start_node = path[0]

        file_name = self.graph.get_node_file_path(start_node)
        cur_node = self.graph.get_node_attr(start_node)
        if file_name is None:
            return False
        file_name = file_name if '/' not in file_name else file_name.split('/')[-1]
        return file_name in file_names

    def start_with_var(self, var_names, path):
        #TODO: not finished, need to update the var name finding algorithm
        """
        check whether a path starts with a variable 
        Args:
            var_names: the possible var names
            path: the path to be checked
        Return:
            True or False
        """
        start_node = path[0]

        path_start_var_name = self.graph.get_name_from_child(start_node)
        cur_node = self.graph.get_node_attr(start_node)
        if path_start_var_name is None:
            return False
        return path_start_var_name in var_names

    def has_user_input(self, _, path):
        """
        check if any node in this path contains user input
        user input is defined as in the http, process or 
        the arguments of the module entrance functions
        
        we check by the obj in the edges
        Args: 
            path: the path
        Return:
            True or False
        """
        pre_node = None
        for node in path:
            if not pre_node:
                pre_node = node;
                continue
            
            cur_edges = self.graph.get_edge_attr(pre_node, node)
            # print("{} --{}--> {}".format(pre_node, cur_edges, node))
            if not cur_edges:
                continue
            for k in cur_edges:
                if 'type:TYPE' in cur_edges[k] and cur_edges[k]['type:TYPE'] == "OBJ_REACHES":
                    obj = cur_edges[k]['obj']
                    obj_attr = self.graph.get_node_attr(obj)
                    if 'tainted' in obj_attr and obj_attr['tainted']:
                        return True
            pre_node = node

            """
            all_child = self.graph.get_all_child_nodes(node)
            objs = []
            for child in all_child:
                objs += self.graph.get_in_edges(child, edge_type='OBJ_TO_AST')
            for obj in objs:
                node_attr = self.graph.get_node_attr(obj[0])
                # here we only keep the obj which in the OBJ_REACHES edges
                if 'tainted' in node_attr and node_attr['tainted']:
                    print(obj[0], node_attr, self.graph.get_node_attr(obj[1]))
                    return True
            """
        if self.start_within_file(['http.js', 'process.js', 'yargs.js'], path):
            return True
        return False

    def check(self, path):
        """
        select the checking function and run it based on the key value
        Return:
            the running result of the obj
        """
        key_map = {
                "exist_func": self.exist_func,
                "not_exist_func": self.not_exist_func,
                "start_with_func": self.start_with_func,
                "not_start_with_func": self.not_start_with_func,
                "start_within_file": self.start_within_file,
                "not_start_within_file": self.not_start_within_file,
                "end_with_func": self.end_with_func,
                "has_user_input": self.has_user_input,
                "start_with_var": self.start_with_var
                }

        if self.key in key_map:
            check_function = key_map[self.key]
        else:
            return False

        return check_function(self.value, path)


class TraceRule(TraceRuleInterface):
    def __init__(self, key, value, G):
        if G.new_trace_rule:
            self.trace_rule = TraceRuleNew(key, value, G)
        else:
            self.trace_rule = TraceRuleOld(key, value, G)
    
    def check(self, path):
        print('checking path', path)
        return self.trace_rule.check(path)
