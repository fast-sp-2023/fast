import argparse
import sys
import sty
from .graph import Graph
from .logger import *
from .opgen import register_func, handle_node, \
    add_edges_between_funcs, analyze_files, analyze_string, generate_obj_graph
from .helpers import get_func_name
from .trace_rule import TraceRule
from .vul_checking import *
from datetime import datetime
import time

def unittest_main(file_path, check_signatures=[], vul_type='os_command',
    args=None, graph=None, original_path=None):
    """
    main function for uniitest 
    """
    if graph is None:
        G = Graph()
    else:
        G = graph
    # if graph is not None:
    #     del graph
    # G = Graph()
    G.exit_when_found = True
    G.vul_type = vul_type
    G.check_proto_pollution = (vul_type == 'proto_pollution')
    G.check_ipt = (vul_type == 'int_prop_tampering')
    if args is not None:
        G.single_branch = args.single_branch
        G.function_time_limit = args.function_timeout
        G.check_proto_pollution = G.check_proto_pollution or args.proto_pollution
        G.check_ipt = G.check_ipt or args.int_prop_tampering
        G.no_file_based = args.nfb
        G.two_pass = args.rcf
        G.rough_call_dist = args.rcd
        G.auto_exploit = args.exploit
        G.coarse_only = args.coarse_only
    G.entry_file_path = original_path
    result = analyze_files(G, file_path, check_signatures=check_signatures)
    # output location of prototype pollution to a seperate file
    proto_pollution_logger = create_logger('proto_pollution',
            output_type='file', file_name="proto_pollution.log")
    if G.proto_pollution:
        proto_pollution_logger.info('Prototype pollution found in package {}'
            .format(G.entry_file_path))
        for ast_node in G.proto_pollution:
            proto_pollution_logger.info('{} {}\n{}'
                .format(ast_node, G.get_node_file_path(ast_node),
                        G.get_node_line_code(ast_node)))
    # IPT output
    ipt_logger = create_logger('ipt',
            output_type='file', file_name="int_prop_tampering.log")
    if G.ipt_use:
        ipt_logger.info('Internal property tampering found in package {}'
            .format(G.entry_file_path))
        if True:
            ipt_logger.info('Write:')
            for ast_node in G.ipt_write:
                ipt_logger.info('{} {}\n{}'
                    .format(ast_node, G.get_node_file_path(ast_node),
                            G.get_node_line_code(ast_node)))
        ipt_logger.info('Use:')
        for ast_node in G.ipt_use:
            ipt_logger.info('{} {}\n{}'
                .format(ast_node, G.get_node_file_path(ast_node),
                        G.get_node_line_code(ast_node)))
    return result, G

def main():
    # Parse arguments
    parser = argparse.ArgumentParser(
        description='Object graph generator for JavaScript.')
    parser.add_argument('-p', '--print', action='store_true',
                        help='Print logs to console, instead of file.')
    parser.add_argument('-t', '--vul-type', default='os_command',
                        help="Set the vulnerability type to be checked.")
    parser.add_argument('-P', '--prototype-pollution', '--pp',
                        action='store_true',
                        help="Check prototype pollution.")
    parser.add_argument('-I', '--int-prop-tampering', '--ipt',
                        action='store_true',
                        help="Check internal property tampering.")
    parser.add_argument('-m', '--module', action='store_true',
                        help="Module mode. Regard the input file as a module "
                        "required by some other modules. This implies -a.")
    parser.add_argument('-q', '--exit', action='store_true', default=False,
                        help="Exit the program when vulnerability is found.")
    parser.add_argument('-s', '--single-branch', action='store_true',
                        help="Single branch. Do not create multiple "
                        "possibilities when meet a branching point.")
    parser.add_argument('-a', '--run-all', action='store_true', default=False,
                        help="Run all exported functions in module.exports. "
                        "By default, only main functions will be run.")
    parser.add_argument('-f', '--function-timeout', type=float,
                        help="Time limit when running all exported function, "
                        "in seconds. (Defaults to no limit.)")
    parser.add_argument('-c', '--call-limit', default=None, type=int,
                        help="Set the limit of a call statement. "
                        "(Defaults to 3.)")
    parser.add_argument('-e', '--entry-func')
    parser.add_argument('-F', '--nfb', '--no-file-based', action='store_true')
    parser.add_argument('-C', '--rcf', '--rough-control-flow', action='store_true')
    parser.add_argument('-D', '--rcd', '--rough-call-distance', action='store_true')
    parser.add_argument('-X', '--exploit', '--auto-exploit', action='store_true')
    parser.add_argument('-i', '--interactive', action='store_true')
    parser.add_argument('-1', '--coarse-only', action='store_true')
    parser.add_argument('input_file', action='store', nargs='?',
        help="Source code file (or directory) to generate object graph for. "
        "Use '-' to get source code from stdin. Ignore this argument to "
        "analyze ./nodes.csv and ./rels.csv.")
    args = parser.parse_args()
    if args.vul_type == 'prototype_pollution' or args.vul_type == 'pp':
        args.vul_type = 'proto_pollution'
    if args.vul_type == 'ipt':
        args.vul_type = 'int_prop_tampering'
    
    logger = create_logger("main_logger", output_type="file")
    start_time = time.time()
    G = Graph()

    if args.exploit:
        G.auto_exploit = args.exploit
        args.module = True
    if args.print or args.interactive:
        level = logging.DEBUG if args.print else logging.INFO
        logger = create_logger("main_logger", output_type="console",
            level=level)
        create_logger("graph_logger", output_type="console",
            level=level)
        G.print = True
    G.run_all = args.run_all or args.module
    G.no_file_based = args.nfb
    G.two_pass = args.rcf
    G.rough_call_dist = args.rcd
    G.function_time_limit = args.function_timeout
    G.exit_when_found = args.exit
    G.single_branch = args.single_branch
    G.vul_type = args.vul_type
    G.func_entry_point = args.entry_func
    G.check_proto_pollution = (args.prototype_pollution or 
                               args.vul_type == 'proto_pollution')
    G.check_ipt = (args.int_prop_tampering or 
                               args.vul_type == 'int_prop_tampering')
    if args.call_limit is not None:
        G.call_limit = args.call_limit
    G.interactive = args.interactive
    G.coarse_only = args.coarse_only

    # Analyze and simulate
    logger.info('Analysis starts at ' +
        datetime.fromtimestamp(start_time).strftime('%Y-%m-%d %H:%M:%S'))
    if args.input_file:
        if args.input_file == '-':
            if args.module:
                raise argparse.ArgumentTypeError(
                    'stdin cannot be used with module mode')
            else:
                # analyze from stdin
                source = sys.stdin.read()
                analyze_string(G, source, generate_graph=True)
        else:
            G.entry_file_path = args.input_file
            if args.module:
                # pretend another file is requiring this module
                script = "var main_func=require('{}');".format(args.input_file)
                analyze_string(G, script, generate_graph=True)
            else:
                # analyze from JS source code files
                analyze_files(G, args.input_file)
    else:
        if args.module:
            raise argparse.ArgumentTypeError(
                'CSV cannot be used with module mode')
        else:
            # analyze from CSVs
            G.import_from_CSV("./nodes.csv", "./rels.csv")
            generate_obj_graph(G, '0')
    total_num_stat = G.get_total_num_statements()
    print("Statements:", len(G.covered_stat), total_num_stat)
    print("Functions:", len(G.covered_func), G.get_total_num_functions())
    # G.relabel_nodes()
    G.export_to_CSV("./opg_nodes.tsv", "./opg_rels.tsv")
    logger.log(ATTENTION, 'Analysis finished at ' +
        datetime.today().strftime('%Y-%m-%d %H:%M:%S') +
        ', Time spent: %.3fs' % (time.time() - start_time))

    # Vulnerability checking
    if G.proto_pollution:
        logger.debug(sty.ef.inverse + 'prototype pollution' + sty.rs.all)

        for ast_node in G.proto_pollution:
            pathes = G._dfs_upper_by_edge_type(ast_node)
            logger.debug('{} {}\n{}'
                .format(sty.fg.li_cyan + ast_node + sty.rs.all,
                    G.get_node_file_path(ast_node),
                    G.get_node_line_code(ast_node)))
        print(G.proto_pollution)

    if G.ipt_use:
        logger.debug(sty.ef.inverse + 'internal property tampering' + sty.rs.all)

        if G.ipt_write:
            logger.debug('Write:')
            for ast_node in G.ipt_write:
                pathes = G._dfs_upper_by_edge_type(ast_node)
                logger.debug('{} {}\n{}'
                    .format(sty.fg.li_cyan + ast_node + sty.rs.all,
                        G.get_node_file_path(ast_node),
                        G.get_node_line_code(ast_node)))
            print(G.ipt_write)
            logger.debug('')
        logger.debug('Use:')
        for ast_node in G.ipt_use:
            pathes = G._dfs_upper_by_edge_type(ast_node)
            logger.debug('{} {}\n{}'
                .format(sty.fg.li_cyan + ast_node + sty.rs.all,
                    G.get_node_file_path(ast_node),
                    G.get_node_line_code(ast_node)))
        print(G.ipt_use)

    if G.vul_type not in ['proto_pollution', 'int_prop_tampering']:
        logger.debug(sty.ef.inverse + G.vul_type + sty.rs.all)
        res_path = traceback(G, G.vul_type)

        logger.debug('ResPath0:')
        logger.debug(res_path[0])
        logger.debug('ResPath1:')
        logger.debug(res_path[1])

        res_pathes = vul_checking(G, res_path[0], G.vul_type)
        print(res_pathes)
        for path in res_pathes:
            res_text_path = get_path_text(G, path, path[0])
            print("Attack Path: ")
            print(res_text_path)

        if len(res_pathes) != 0:
            with open('vul_func_names.csv', 'a') as fp:
                logger.log(ATTENTION, f'{G.vul_type} successfully found in '
                            f'{G.entry_file_path} at main?')
                fp.write(f'{G.vul_type},"{G.entry_file_path}","main","",{len(res_path)}\n')
            G.success_detect = True

    if G.success_detect:
        print(sty.fg.green + sty.ef.b + 'Detection: successful' + sty.rs.all)
    else:
        print(sty.fg.yellow + sty.ef.b + 'Detection: failed' + sty.rs.all)
    if G.auto_exploit:
        if G.success_exploit:
            print(sty.fg.green + sty.ef.b + 'Exploit: successful' + sty.rs.all)
        else:
            print(sty.fg.yellow + sty.ef.b + 'Exploit: failed' + sty.rs.all)
    else:
        print(sty.fg.da_grey + sty.ef.b + 'Exploit: turned off' + sty.rs.all)
    logger.debug('Time spent: %.3fs' % (time.time() - start_time))
    if G.exit_when_found and G.finished:
        print(sty.ef.b + 'Analysis stopped after vulernability is found. Only the first few CF paths are kept.' + sty.rs.all)
    vul_files = list(map(lambda p: os.path.relpath(p, G.entry_file_path), G.vul_files))
    print(sty.ef.b + f'Vulnerable files: {vul_files}' + sty.rs.all)
    print(sty.fg.li_magenta + sty.ef.b +
        f'Number of CF Paths: {G.num_of_cf_paths}' + sty.rs.all)
    print(sty.fg.li_magenta + sty.ef.b +
        f'Number of Preceding CF Paths: {G.num_of_prec_cf_paths}' + sty.rs.all)
    print(sty.fg.li_magenta + sty.ef.b +
        f'Number of Full CF Paths: {G.num_of_full_cf_paths}' + sty.rs.all)
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
    for e in call_edges:
        l0 = G.get_node_attr(e[0]).get('labels:label')
        if l0 is None or l0.startswith('Artificial'):
            continue
        l1 = G.get_node_attr(e[1]).get('labels:label')
        if l1 is None or l1.startswith('Artificial'):
            continue
        real_ce_counter += 1
        real_call_edges.append(e)
    print(sty.fg.li_magenta +
            f'Number of CF Edges: ' + sty.rs.all + f'{len(cf_edges)}')
    print(sty.fg.li_magenta +
            f'Number of Real CF Edges: ' + sty.rs.all + f'{real_cf_counter}')
    print(sty.fg.li_magenta +
            f'Number of Call Edges: ' + sty.rs.all + f'{len(call_edges)}')
    print(sty.fg.li_magenta +
            f'Number of Real Call Edges: ' + sty.rs.all + f'{real_ce_counter}')
    # print(real_call_edges)
    covered_stmt = len(G.covered_stat)
    total_stmt = G.get_total_num_statements()
    # print(sty.fg.li_yellow + f'Code coverage: ' + sty.rs.all + 
    #         f'{covered_stmt / total_stmt * 100:.2f}%'
    #         + f' {covered_stmt}/{total_stmt}'
    #         )
    print(sty.fg.li_magenta + f'Number of Dynamically Resolvable Calls: ' +
                            sty.rs.all + f'{len(G.dynamic_calls)}')
    print(sty.fg.li_magenta + f'Number of Statically Resolvable Calls: ' +
                            sty.rs.all + f'{len(G.static_calls)}')
    print(sty.fg.li_magenta + f'Number of Unresolvable Calls: ' +
                            sty.rs.all + f'{len(G.unresolvable_calls)}')
    print(sty.fg.li_magenta + f'Number of Function Calls: ' +
                            sty.rs.all + f'{len(G.total_calls)}')
    print(sty.fg.li_magenta + f'Number of Rerun: ' +
                            sty.rs.all + f'{G.rerun_counter}')
