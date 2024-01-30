from . import opgen
from .graph import Graph
from .utilities import wildcard
from collections import defaultdict
from functools import reduce
from operator import add
import sty
import re
import z3
import time

class MixedSymbol:
    def __init__(self, name, _type=None):
        super().__init__()
        self._number = None
        self._string = None
        if _type == 'number':
            self._number = z3.Real(f'n{name}')
        elif _type == 'string':
            self._string = z3.String(f's{name}')
        else:
            self._number = z3.Real(f'n{name}')
            self._string = z3.String(f's{name}')

    def number(self):
        return self._number

    def string(self):
        return self._string


def check_number_operation(arr):
    for i in arr:
        if type(i) is not MixedSymbol:
            return False
        elif i.number() is None:
            return False
    return True


def check_string_operation(arr):
    for i in arr:
        if type(i) is not MixedSymbol:
            return False
        elif i.string() is None:
            return False
    return True
    

def solve2(G: Graph, final_objs, initial_objs=None, contains=True):
    time1 = time.time()
    print('final objs:', final_objs, 'value:', G.solve_from, 'initial objs:', initial_objs)
    solver = None
    symbols = None
    def symbol(obj):
        nonlocal G, symbols, solver
        if obj not in symbols:
            t = G.get_node_attr(obj).get('type')
            v = G.get_node_attr(obj).get('code')
            s = symbols[obj] = MixedSymbol(obj, t)
            if v != wildcard:
                if t == 'string':
                    if obj in final_objs and contains:
                        solver.add(z3.Contains(s.string(), v)) # str contains
                        # solver.add(z3.InRe(s.string(), z3.Re(v))) # regex
                    else:
                        solver.add(s.string() == z3.StringVal(v))
                        # print(sty.fg.da_grey, f'{s.string()} == {z3.StringVal(v)}', sty.rs.all)
                elif t == 'number':
                    solver.add(s.number() == v)
        return symbols[obj]
    for final_obj in final_objs:
        original_type = G.get_node_attr(final_obj).get('type')
        original_value = G.get_node_attr(final_obj).get('code')
        if type(G.solve_from) in [int, float]:
            G.set_node_attr(final_obj, ('type', 'number'))
        elif type(G.solve_from) == str:
            G.set_node_attr(final_obj, ('type', 'string'))
        G.set_node_attr(final_obj, ('code', G.solve_from))

        solver = z3.Solver()
        symbols = defaultdict(MixedSymbol)
        q = [final_obj]
        # in case the sink function's parameter is exactly an exported
        # function's parameter
        symbol(final_obj)
        
        while q:
            head = q.pop(0)
            _contributors = [] # item: (opt, contributor)
            contributors = defaultdict(list) # opt[:2] -> list[contributor]
            # sort and group contributors by operations and operation value index (opt[:2])
            # print(sty.fg.da_grey, head, '<-', G.get_in_edges(head, edge_type='CONTRIBUTES_TO'), sty.rs.all)
            for e in G.get_in_edges(head, edge_type='CONTRIBUTES_TO'):
                opt = e[-1].get('opt') # operation tag
                if opt is None:
                    continue
                if e[0] not in q:
                    q.append(e[0])
                _contributors.append((opt, e[0]))
            _contributors = sorted(_contributors)
            for opt, c in _contributors:
                contributors[(opt[0], opt[1])].append(c)
            # print(sty.fg.da_grey, head, '<-', contributors, sty.rs.all)
            # check and convert operations to rules (constraints)
            for opt, cl in contributors.items():
                if opt[0] == 'string_concat':
                    if check_string_operation(map(symbol, [head] + cl)):
                        cl_string_symbols = list(map(lambda x: symbol(x).string(), cl))
                        # print(sty.fg.da_grey, f'{symbol(head).string()} == Concat({cl_string_symbols})', sty.rs.all)
                        if len(cl_string_symbols) == 1:
                            solver.add(symbol(head).string() == cl_string_symbols[0])
                        else:
                            solver.add(symbol(head).string() == z3.Concat(*cl_string_symbols))
                    else:
                        print(f'ERROR: Checking {cl} for string_concat failed!')
                elif opt[0] == 'numeric_add':
                    if check_number_operation(map(symbol, [head] + cl)):
                        cl_number_symbols = list(map(lambda x: symbol(x).number(), cl))
                        if len(cl_number_symbols) == 1:
                            solver.add(symbol(head).number() == cl_number_symbols[0])
                        else:
                            solver.add(symbol(head).number() == reduce(add, cl_number_symbols))
                    else:
                        print(f'ERROR: Checking {cl} for numeric_add failed!')
                elif opt[0] == 'unknown_add':
                    if check_string_operation(map(symbol, [head] + cl)):
                        cl_string_symbols = list(map(lambda x: symbol(x).string(), cl))
                        if len(cl_string_symbols) == 1:
                            solver.add(symbol(head).string() == cl_string_symbols[0])
                        else:
                            solver.add(symbol(head).string() == z3.Concat(*cl_string_symbols))
                        # print(f'{head} = concat({cl})')
                    elif check_number_operation(map(symbol, [head] + cl)):
                        cl_number_symbols = list(map(lambda x: symbol(x).number(), cl))
                        if len(cl_number_symbols) == 1:
                            solver.add(symbol(head).number() == cl_number_symbols[0])
                        else:
                            solver.add(symbol(head).number() == reduce(add, cl_number_symbols))
                        # print(f'{head} = add({cl})')
                    else:
                        print(f'ERROR: Checking {cl} for unknown_add failed!')
                else:
                    # print(f'ERROR: {opt[0]} on {cl} does not match any operation!')
                    pass
            
        for targets, rule, literal in G.extra_constraints:
            for target in targets:
                if type(literal) == str:
                    sym = symbol(target).string()
                    if rule == 'not-contains':
                        if sym is not None:
                            solver.add(z3.Not(z3.Contains(sym, z3.StringVal(literal))))
                    elif rule == 'contains':
                        if sym is not None:
                            solver.add(z3.Contains(sym, z3.StringVal(literal)))

        # solver.add(z3.Not(z3.PrefixOf(z3.StringVal('"'), symbol(final_obj).string())))
        solver.add(z3.Not(z3.PrefixOf(z3.StringVal(';'), symbol(final_obj).string())))
        solver.add(z3.Not(z3.PrefixOf(z3.StringVal('&'), symbol(final_obj).string())))

        G.set_node_attr(final_obj, ('type', original_type))
        G.set_node_attr(final_obj, ('code', original_value))
        solver.set(timeout=2000)
        path_results = {}
        try:
            if solver.check() == z3.unsat:
                # print(solver.assertions())
                yield solver.assertions(), 'failed'
                continue
            model = solver.model()
        except z3.Z3Exception:
            yield solver.assertions(), 'failed'
            continue
        for var in model:
            vn = str(var)
            if vn in path_results:
                print('ERROR: duplicated variable' + vn)
            if initial_objs and vn[1:] not in initial_objs:
                continue
            # if vn[1:] in G.reverse_names:
            if G.reverse_names[vn[1:]]:
                name = ', '.join(G.reverse_names[vn[1:]])
                path_results[vn] = (name, model[var])
            else:
                # results[vn] = model[var]
                pass
        # results.append(solver.assertions(), path_results)
        yield (solver.assertions(), path_results)
    G.solver_time += time.time() - time1


def solve1(G: Graph, final_objs, initial_objs=None, contains=True):
    results = []
    def get_symbol(obj):
        nonlocal G, symbol, solver
        if obj not in symbol:
            t = G.get_node_attr(obj).get('type')
            v = G.get_node_attr(obj).get('code')
            # print('type =', t, 'value =', v)
            if t == 'number':
                symbol[obj] = z3.Real(f'n{obj}')
                solver.add(symbol[obj] == float(v))
            elif t == 'string':
                symbol[obj] = z3.String(f's{obj}')
                if obj in final_objs and contains:
                    solver.add(z3.Contains(symbol[obj], v)) # str contains
                    # solver.add(z3.InRe(symbol[obj], z3.Re(v))) # regex
                else:
                    solver.add(symbol[obj] == z3.StringVal(v))
            # elif v == wildcard or t == 'object':
            else:
                symbol[obj] = (z3.Real(f'n{obj}'), z3.String(f's{obj}'))
    for final_obj in final_objs:
        original_type = G.get_node_attr(final_obj).get('type')
        original_value = G.get_node_attr(final_obj).get('code')
        if type(G.solve_from) in [int, float]:
            G.set_node_attr(final_obj, ('type', 'number'))
        elif type(G.solve_from) == str:
            G.set_node_attr(final_obj, ('type', 'string'))
        G.set_node_attr(final_obj, ('code', G.solve_from))
        symbol = {}
        solver = z3.Solver()
        
        q = [final_obj]
        get_symbol(final_obj)
        # visited_objs = set()
        while q:
            obj = q.pop(0)
            contributors = []
            in_edges = G.get_in_edges(obj, edge_type='CONTRIBUTES_TO')
            print(in_edges)
            for e in in_edges:
                op = e[-1].get('op', '')
                contributors.append((op, e[0]))
                if e[0] not in q:
                    q.append(e[0])
            contributors = sorted(contributors)
            for tag1, source1 in contributors:
                match = re.match(r'(\w+)#(\w+)', tag1)
                if not match:
                    continue
                op, order = match.groups()
                if order != '0':
                    continue
                get_symbol(source1)
                for tag2, source2 in contributors:
                    get_symbol(source2)
                    if tag2 == f'{op}#1':
                        if type(symbol[source1]) == tuple:
                            if type(symbol[source2]) == tuple:
                                if type(symbol[obj]) == tuple:
                                    if tag1.startswith('numeric_add') or tag1.startswith('unknown_add'):
                                        solver.add(symbol[source1][0] + symbol[source2][0] == symbol[obj][0])
                                    if tag1.startswith('string_concat') or tag1.startswith('unknown_add'):
                                        solver.add(symbol[source1][1] + symbol[source2][1] == symbol[obj][1])
                                elif type(symbol[obj]) == z3.ArithRef:
                                    if tag1.startswith('numeric_add') or tag1.startswith('unknown_add'):
                                        solver.add(symbol[source1][0] + symbol[source2][0] == symbol[obj])
                                elif type(symbol[obj]) == z3.SeqRef:
                                    if tag1.startswith('numeric_add') or tag1.startswith('unknown_add'):
                                        solver.add(symbol[source1][1] + symbol[source2][1] == symbol[obj])
                            elif type(symbol[source2]) == z3.ArithRef:
                                if type(symbol[obj]) == tuple:
                                    if tag1.startswith('numeric_add') or tag1.startswith('unknown_add'):
                                        solver.add(symbol[source1][0] + symbol[source2] == symbol[obj][0])
                                elif type(symbol[obj]) == z3.ArithRef:
                                    if tag1.startswith('numeric_add') or tag1.startswith('unknown_add'):
                                        solver.add(symbol[source1][0] + symbol[source2] == symbol[obj])
                            elif type(symbol[source2]) == z3.SeqRef:
                                if type(symbol[obj]) == tuple:
                                    if tag1.startswith('string_concat') or tag1.startswith('unknown_add'):
                                        solver.add(symbol[source1][1] + symbol[source2] == symbol[obj][1])
                                elif type(symbol[obj]) == z3.SeqRef:
                                    if tag1.startswith('string_concat') or tag1.startswith('unknown_add'):
                                        solver.add(symbol[source1][1] + symbol[source2] == symbol[obj])
                        elif type(symbol[source1]) == z3.ArithRef:
                            if type(symbol[source2]) == tuple:
                                if type(symbol[obj]) == tuple:
                                    if tag1.startswith('numeric_add') or tag1.startswith('unknown_add'):
                                        solver.add(symbol[source1] + symbol[source2][0] == symbol[obj][0])
                                elif type(symbol[obj]) == z3.ArithRef:
                                    if tag1.startswith('numeric_add') or tag1.startswith('unknown_add'):
                                        solver.add(symbol[source1] + symbol[source2][0] == symbol[obj])
                            elif type(symbol[source2]) == z3.ArithRef:
                                if type(symbol[obj]) == tuple:
                                    if tag1.startswith('numeric_add') or tag1.startswith('unknown_add'):
                                        solver.add(symbol[source1] + symbol[source2] == symbol[obj][0])
                                elif type(symbol[obj]) == z3.ArithRef:
                                    if tag1.startswith('numeric_add') or tag1.startswith('unknown_add'):
                                        solver.add(symbol[source1] + symbol[source2] == symbol[obj])
                        elif type(symbol[source1]) == z3.SeqRef:
                            if type(symbol[source2]) == tuple:
                                if type(symbol[obj]) == tuple:
                                    if tag1.startswith('string_concat') or tag1.startswith('unknown_add'):
                                        solver.add(symbol[source1] + symbol[source2][1] == symbol[obj][1])
                                elif type(symbol[obj]) == z3.SeqRef:
                                    if tag1.startswith('string_concat') or tag1.startswith('unknown_add'):
                                        solver.add(symbol[source1] + symbol[source2][1] == symbol[obj])
                            elif type(symbol[source2]) == z3.SeqRef:
                                if type(symbol[obj]) == tuple:
                                    if tag1.startswith('string_concat') or tag1.startswith('unknown_add'):
                                        solver.add(symbol[source1] + symbol[source2] == symbol[obj][1])
                                elif type(symbol[obj]) == z3.SeqRef:
                                    if tag1.startswith('string_concat') or tag1.startswith('unknown_add'):
                                        solver.add(symbol[source1] + symbol[source2] == symbol[obj])
                        break
        for targets, rule, literal in G.extra_constraints:
            for target in targets:
                if type(literal) == str:
                    get_symbol(target)
                    if type(symbol[target]) == tuple:
                        if rule == 'not-contains':
                            solver.add(z3.Not(z3.Contains(symbol[target][1], z3.StringVal(literal))))
                        elif rule == 'contains':
                            solver.add(z3.Contains(symbol[target][1], z3.StringVal(literal)))
                        # elif rule == 'contains':
                    elif type(symbol[target]) == z3.SeqRef:
                        if rule == 'not-contains':
                            solver.add(z3.Not(z3.Contains(symbol[target], z3.StringVal(literal))))
                        elif rule == 'contains':
                            solver.add(z3.Contains(symbol[target], z3.StringVal(literal)))
        G.set_node_attr(final_obj, ('type', original_type))
        G.set_node_attr(final_obj, ('code', original_value))
        solver.set(timeout=30000)
        path_results = defaultdict(list)
        try:
            if solver.check() == z3.unsat:
                # print(solver.assertions())
                yield (solver.assertions(), 'failed')
                continue
            model = solver.model()
        except z3.Z3Exception:
            yield (solver.assertions(), 'failed')
            continue
        for var in model:
            vn = str(var)
            if initial_objs and vn[1:] not in initial_objs:
                continue
            # if vn[1:] in G.reverse_names:
            if G.reverse_names[vn[1:]]:
                name = ', '.join(G.reverse_names[vn[1:]]) + f'({vn})'
                path_results[name].append(model[var])
            else:
                # results[vn] = model[var]
                pass
        # results.append(solver.assertions(), path_results)
        yield (solver.assertions(), path_results or 'timeout')
    # return results

solve = solve2
