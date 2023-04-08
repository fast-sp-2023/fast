from nis import match
import os
import json
import shutil 
import traceback as tb
from tqdm import tqdm
import subprocess
from func_timeout import func_timeout, FunctionTimedOut
import threading
import argparse
import uuid
import gc
import sys
import time
import hashlib
sys.path.append("..")
from simurun.launcher import unittest_main
from simurun.logger import *
from simurun.trace_rule import TraceRule
from simurun.vul_checking import *
from simurun.vul_func_lists import *
from simurun.graph import Graph

skip_packages = []

args = None
root_path = None

npm_test_logger = create_logger("npmtest", output_type = "file", level=10, file_name="npmtest.log")
npm_run_logger = create_logger("npmrun", output_type = "file", level=10, file_name="npmrun.log")
# npm_run_time_logger = create_logger("npmruntime", output_type = "file", level=10, file_name="npmrun_time.log")
npm_code_cov_logger = create_logger("npmcc", output_type = "file", level=10, file_name="npm_code_coverage.log")
npm_cf_stats_logger = create_logger("npmcfstats", output_type = "file", level=10, file_name="npm_cf_stats.csv")
npm_exploit_logger = None

def validate_package(package_path):
    """
    check whether a package is valid by whether it include package.json
    Args:
        package_path: the path to the package
    Returns:
        True or False
    """
    package_json_path = '{}/package.json'.format(package_path)
    index_path = os.path.join(package_path, 'index.js')
    return os.path.exists(package_json_path) or os.path.exists(index_path)
    
def get_list_of_packages(path, start_id=None, size=None, use_cache=True):
    """
    return a list of package names, which is the name of the folders in the path
    Args:
        path: the path of packages folder
    return:
        a list of package names
    """
    path = path.rstrip(r'\/')
    path_hash = hashlib.md5(path.encode('utf-8')).hexdigest()[:6]

    if use_cache and os.path.exists(f'all_packages_{path_hash}.json'):
        with open(f'all_packages_{path_hash}.json', 'r') as json_file:
            _json = json.load(json_file)
            if _json.get('path') == path:
                npm_run_logger.info(f"Loaded package list from all_packages_{path_hash}.json")
                return _json.get('packages')

    possible_packages = [os.path.join(path, name) for name in os.listdir(path)]


    if start_id is not None:
        possible_packages = possible_packages[start_id:]
    if size is not None:
        possible_packages = possible_packages[:size]
    
    all_packages = []
    print("Preparing, path hash", path_hash)
    cnt = 0
    for package in tqdm(possible_packages):
        if not (os.path.isdir(package) or (os.path.isfile(package) and (
                package.endswith('.tgz') or package.endswith('.tar.gz')))):
            continue
        # print(package)
        if package.split('/')[-1][0] == '@' and (not validate_package(package)):
            #should have sub dir
            sub_packages = [os.path.join(package, name) for name in os.listdir(package)]
            all_packages += sub_packages
        else:
            all_packages.append(package)
        cnt += 1
        if cnt % 1000 == 0:
            print('where the fuck did you write?', f'all_packages_{path_hash}.json')
            with open(f'all_packages_{path_hash}.json', 'w') as of:
                json.dump({"path": path, "packages": all_packages}, of)

    
    print('Prepared')
    if use_cache and len(all_packages) > 100:
        with open(f'all_packages_{path_hash}.json', 'w') as of:
            json.dump({"path": path, "packages": all_packages}, of)
    
    return all_packages 

def get_entrance_files_of_package(package_path, get_all=False):
    """
    get the entrance file pathes of a package
    we use madge to get all the entrance functions, which are the files that no one require
    at the same time if the main file of the package json is not included
    include the main file into the list
    Args:
        package: the path of a package
    return:
        the main entrance files of the library
    """

    entrance_files = []
    package_json_path = os.path.join(package_path, 'package.json')
    main_files = []

    if not validate_package(package_path):
        print("ERROR: {} do not exist".format(package_json_path)) 
        return None

    if not os.path.exists(package_json_path):
        # index based
        return [os.path.join(package_path, 'index.js')]

    with open(package_json_path) as fp:
        package_json = {}
        try:
            package_json = json.load(fp)
        except:
            npm_test_logger.error("Special {}".format(package_path))


        if 'main' not in package_json:
            main_file = 'index.js'
        else:
            main_file = package_json['main']

        if 'bin' in package_json:
            if type(package_json['bin']) == str:
                main_files.append(package_json['bin'])
            else:
                for key in package_json['bin']:
                    main_files.append(package_json['bin'][key])

    print("path ", main_files)
    # entrance file maybe two different formats
    # ./index = ./index.js or ./index = ./index/index.js
    if main_file[-3:] != ".js":
        main_files.append(main_file + "/index.js")
        main_file += '.js'

    main_files.append(main_file)

    if get_all:
        analysis_path = os.path.normpath(__file__ + '/../require_analysis.js')
        proc = subprocess.Popen(['node', analysis_path,
            package_path], text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        stdout, stderr = proc.communicate()
        #here we assume that there are no ' in the file names
        #print(stdout)
        stdout = stdout.replace('\'', '"')
        package_structure = json.loads(stdout)

        for root_file in package_structure:
            if not root_file.endswith('.min.js'):
                entrance_files.append(root_file)

    for main_file in main_files:
        if main_file not in entrance_files and os.path.exists("{}/{}".format(package_path, main_file)):
            entrance_files.append(main_file)

    main_file_pathes = ["{}/{}".format(package_path, main_file) for main_file in entrance_files]
    print("Entrance Files ", main_file_pathes)

    return main_file_pathes

def item_line_count(path):
    if os.path.isdir(path):
        return dir_line_count(path)
    elif os.path.isfile(path):
        return len(open(path, 'rb').readlines())
    else:
        return 0

def item_size_count(path):
    if os.path.isdir(path):
        return dir_line_count(path)
    elif os.path.isfile(path):
        if path.split('.')[-1] != 'js':
            return 0
        return os.path.getsize(path)
    else:
        return 0

def dir_line_count(dir):
    return sum(map(lambda item: item_line_count(os.path.join(dir, item)), os.listdir(dir)))

def dir_size_count(dir):
    return sum(map(lambda item: item_size_count(os.path.join(dir, item)), os.listdir(dir)))

def unit_check_log(G, vul_type, package=None):
    """
    run the check and log the result
    """
    res_path = traceback(G, vul_type)
    line_path = res_path[0]
    detailed_path = res_path[1]
    caller_list = res_path[2]
    checking_res = vul_checking(G, line_path, vul_type)

    if (len(line_path) != 0 or len(caller_list) != 0) and len(checking_res) != 0:
        """
        print("Found path from {}: {}\n".format(package, checking_res))
        with open("found_path_{}.log".format(vul_type), 'a+') as fp:
            fp.write("{} called".format(caller_list))
            fp.write("Found path from {}: {}\n".format(package, checking_res))
        """
        return 1
    else:
        """
        with open("not_found_path_{}.log".format(vul_type), 'a+') as fp:
            fp.write("{} called".format(caller_list))
            fp.write("Not Found path from {}: {}\n".format(package, checking_res))
        """
        return 0

def test_package(package_path, vul_type='os_command', graph=None):
    # TODO: change the return value
    """
    test a specific package
    Args:
        package_name: the name of the package
    return:
        the result:
            1, success
            -2, not found. package parse error
            -3, graph generation error
    """
    # pre-filtering the signature functions by grep

    line_count = dir_line_count(package_path)
    size_count = dir_size_count(package_path)
    npm_test_logger.info("Running {}, size: {}, cloc: {}".format(package_path, size_count, line_count))
    # graph.LOC = line_count
    # graph.SIZE = size_count

    # the main generating program can solve the main file
    # but we also get the entrance files
    package_main_files = get_entrance_files_of_package(package_path, get_all=True)
    detect_res = []
    exploit_res = []

    if package_main_files is None:
        return [], []

    for package_file in package_main_files:
        res1, res2 = test_file(package_file, vul_type, graph)
        detect_res.append(res1)
        exploit_res.append(res2)
        # if test_res == 1:
        #     # successfully found
        #     npm_test_logger.info("Finished {}, size: {}, cloc: {}".format(package_path, size_count, line_count))
        #     return res

    npm_test_logger.info("Finished {}, size: {}, cloc: {}".format(package_path, size_count, line_count))
    return detect_res, exploit_res

def output_cf_stats(G, file_path):
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
    covered_stmt = len(G.covered_stat)
    total_stmt = G.get_total_num_statements()
    npm_cf_stats_logger.info(','.join(map(str, ['"' + file_path + '"', len(cf_edges),
        real_cf_counter, f'{covered_stmt / total_stmt * 100:.2f}',
        covered_stmt, total_stmt, len(G.dynamic_calls), len(G.static_calls),
        len(G.unresolvable_calls), len(G.total_calls),
        G.rerun_counter])))

def test_file(file_path, vul_type='xss', graph=None):
    """
    test a specific file 
    Args:
        file_path: the path of the file 
    return:
        the result:
            1, success
            -4, skipped no signaures
            -2, not found file. 
            -3, graph generation error
    """

    global args
    print("Testing {} {}".format(vul_type, file_path))
    if file_path is None:
        npm_test_logger.error("{} not found".format(file_path))
        return -2, 0

    if not os.path.exists('./run_tmp'):
        os.mkdir('./run_tmp')

    test_file_name = "./run_tmp/{}_{}.js".format(file_path.split('/')[-1], str(uuid.uuid4()))
    js_call_templete = "var main_func=require('{}');".format(file_path)
    with open(test_file_name, 'w') as jcp:
        jcp.write(js_call_templete)

    G = None
    try:
        if vul_type == 'proto_pollution' or vul_type == 'int_prop_tampering':
            result, G = unittest_main(test_file_name, vul_type=vul_type,
                args=args, graph=graph, original_path=file_path)
        else:
            result, G = unittest_main(test_file_name, vul_type=vul_type,
                args=args, graph=graph, original_path=file_path,
                check_signatures=get_all_sign_list())
        covered_stmt = len(G.covered_stat)
        total_stmt = G.get_total_num_statements()
        npm_code_cov_logger.info("{}\t{:.2f}\t{}\t{}".format(file_path, covered_stmt / total_stmt * 100, covered_stmt, total_stmt))
        output_cf_stats(G, file_path)
    except Exception as e:
        os.remove(test_file_name)
        npm_test_logger.error("ERROR when generate graph for {}.".format(file_path))
        npm_test_logger.error(e)
        npm_test_logger.debug(tb.format_exc())
        del G
        return -3, 0

    npm_exploit_logger.info("{} finished {} run(s)".format(file_path, G.finished_num_of_passes))
    
    try:
        os.remove(test_file_name)
        #os.remove("run_log.log")
        os.remove("out.dat")
    except:
        pass

    if result == -1:
        npm_test_logger.error("Skip {} for no signature functions".format(file_path))
        del G
        return -4, 0
    elif result == -2:
        npm_test_logger.error("Skip {} for no CF paths found".format(file_path))
        del G
        return -4, 0

    if vul_type == 'proto_pollution':
        final_res = 1 if G.proto_pollution else 0
    elif vul_type == 'int_prop_tampering':
        final_res = 1 if G.ipt_use else 0
    else:
        final_res = unit_check_log(G, vul_type, file_path)

    if G.auto_exploit:
        exploit_res = 1 if G.success_exploit else 0
    else:
        exploit_res = -1

    # final_res = None
    # not necessary but just in case
    del G
    return final_res, exploit_res

def main():
    global root_path, skip_packages, args, npm_exploit_logger
    argparser = argparse.ArgumentParser()
    argparser.add_argument('-c', nargs=2)
    argparser.add_argument('-p', '--print', action='store_true')
    argparser.add_argument('-t', '--vul-type', required=True)
    argparser.add_argument('-l', '--timeout', type=float)
    argparser.add_argument('-f', '--function-timeout', type=float)
    argparser.add_argument('-s', '--single-branch', action='store_true')
    argparser.add_argument('-L', '--package-list')
    argparser.add_argument('-P', '--proto-pollution', action='store_true')
    argparser.add_argument('-I', '--int-prop-tampering', action='store_true')
    argparser.add_argument('-F', '--nfb', '--no-file-based', action='store_true')
    argparser.add_argument('-C', '--rcf', '--rough-control-flow', action='store_true')
    argparser.add_argument('-D', '--rcd', '--rough-call-dist', action='store_true')
    argparser.add_argument('-X', '--exploit', '--auto-exploit', action='store_true')
    argparser.add_argument('-1', '--coarse-only', action='store_true')
    argparser.add_argument('root_path', action='store', nargs=1)

    args = argparser.parse_args()

    chunk_detail = args.c

    if args.vul_type == 'prototype_pollution' or args.vul_type == 'pp':
        args.vul_type = 'proto_pollution'
    if args.vul_type == 'ipt':
        args.vul_type = 'int_prop_tampering'
    if args.print:
        create_logger("main_logger", output_type="console",
                      level=logging.DEBUG)
        create_logger("graph_logger", output_type="console",
                      level=logging.DEBUG)
        create_logger("npmtest", output_type="console",
                      level=logging.DEBUG)

    if args.root_path is not None:
        root_path = args.root_path[0]
    else:
        print("ERROR: {}".format("Please provide a valid testing path"))

    testing_packages = []

    # accept a list of packages within a file
    # the file name does not have version numbers
    # we need a map and assume all packages only have one version
    all_packages_list = get_list_of_packages(root_path, start_id=0)
    package_version_map = {}
    for package_version in all_packages_list:
        if package_version.endswith('.tgz'):
            match = re.match(r'(.+)-([0-9.]+).tgz', package_version)
            if match:
                package_version_map[match[1]] = match[0]
        else:
            # package = package_version.split("@")[0]
            package = '@'.join(package_version.split("@")[:1])
            package_version_map[package] = package_version

    if args.package_list is not None:
        print("Prepareing packages")
        _, file_ext = os.path.splitext(args.package_list)

        with open(args.package_list, 'r') as f:
            if file_ext == '.json':
                names = json.load(f)
            else:
                names = f.readlines()
            for line in tqdm(names):
                testing_package = os.path.join(root_path, line).strip()
                if '@' not in testing_package: # support packages with version numbers
                    if testing_package not in package_version_map:
                        continue
                    testing_package = package_version_map[testing_package]
                testing_packages.append(testing_package)

    # single
    if len(testing_packages) == 0 and args.package_list is None:
        packages = all_packages_list
        # get_list_of_packages(root_path, start_id=0, size=300000)
    else:
        testing_packages = [os.path.join(root_path, t) for t in testing_packages]
        packages = testing_packages

    if len(skip_packages) != 0:
        packages = [package for package in packages if package not in skip_packages]
    
    vul_type = None
    timeout = 30
    # set number of packages
    packages = packages[0:100000]

    # jsTap
    jstap_vul_sink_map = {
        "os_command": ["exec", "execFile", "execSync", "spawn", "spawnSync"],
        "code_exec": ["exec", "eval", "execFile"],
        "path_traversal": ["end", "write"]
    }

    if args.vul_type is not None:
        vul_type = args.vul_type
    if args.timeout is not None:
        timeout = args.timeout

    success_list = []
    skip_list = []
    not_found = []
    generate_error = []
    total_cnt = len(packages)
    cur_cnt = 0
    thread_pool = {}

    if total_cnt == 0:
        return

    start_id = 0 
    end_id = 2147483647

    if chunk_detail is not None:
        worker_id = int(chunk_detail[0]) - 1
        num_workers = int(chunk_detail[1])
        start_id = int(worker_id * total_cnt / num_workers)
        end_id = int((worker_id + 1) * total_cnt / num_workers)
        if worker_id == num_workers - 1:
            end_id = total_cnt 

    npm_res_logger = create_logger("npmres", output_type = "file", level=10, file_name="npmres_{}.log".format(vul_type))
    npm_success_logger = create_logger("npmsuccess", output_type = "file", level=10, file_name="npmsuccess_{}.log".format(vul_type))
    npm_exploit_logger = create_logger("npmexploit", output_type = "file", level=10, file_name="npmexploit_{}.log".format(vul_type))

    os.makedirs('./extracted_packages', exist_ok=True)

    packages = packages[start_id: end_id]
    tqdm_bar = tqdm(packages)
    for package in tqdm_bar:
        cur_cnt += 1

        process_num = int(chunk_detail[0]) - 1 if chunk_detail else 0
        npm_test_logger.info("Process {}, Package {}".format(process_num, cur_cnt))
        npm_run_logger.info("Process {}, Package {}, start {}".format(process_num, cur_cnt, package))
        tqdm_bar.set_description("Process {}, Package {}, {}".format(process_num, cur_cnt, package.split('/')[-1]))
        tqdm_bar.refresh()
        ret_value = 100
        result = []
        G = None # don't initiate G here

        # extract .tgz
        tgz_extract_path = None
        if package.endswith('.tgz'):
            package_name = os.path.splitext(os.path.relpath(package, root_path))[0]
            tgz_extract_path = os.path.abspath(os.path.join(
                './extracted_packages', package_name + '-' + vul_type))
            # tgz_extract_path = os.path.abspath(os.path.join('./extracted_packages', 
            #     hashlib.md5(package.encode('utf-8')).hexdigest()[:10] + '-' + vul_type))
            print(package_name)
            print(tgz_extract_path)
            if not os.path.exists(tgz_extract_path):
                os.mkdir(tgz_extract_path)
            subprocess.run(["tar", "-xzf", package, "-C", tgz_extract_path])
            package = tgz_extract_path + '/package'

        start_time = time.time()
        try:
            result, exploit_result = func_timeout(timeout, test_package, args=(package, vul_type))
            # if len(result) != 0:
            #     # only validate package should be considered
            #     end_time = time.time()
            #     npm_run_time_logger.info("{}\t{}".format(package, end_time - start_time))

        except FunctionTimedOut:
            npm_res_logger.error("{} takes more than {} seconds".format(package, timeout))
            skip_list.append(package)
            print('{} timed out'.format(package))
            # end_time = time.time()
            # npm_run_time_logger.info("{}\t{}".format(package, end_time - start_time))
            # if tgz_extract_path is not None and os.path.exists(tgz_extract_path):
            #     shutil.rmtree(tgz_extract_path)
            continue
        except Exception as e:
            npm_res_logger.error("{} ERROR generating {}".format(package, e))
            tb.print_exc()
            # if tgz_extract_path is not None and os.path.exists(tgz_extract_path):
            #     shutil.rmtree(tgz_extract_path)
            continue

        # if G.get_total_num_statements() > 10 and G.LOC > 10 and \
        #         (1 in result or all(v == 0 for v in result)):
        #     # avoid divide 0
        #     total_num_functions = G.get_total_num_functions()
        #     if total_num_functions == 0:
        #         function_percentage = 0
        #     else:
        #         function_percentage = len(G.covered_func) / total_num_functions

        #     """
        #     print(G.all_stat - G.covered_stat, len(G.covered_stat), len(G.all_stat), G.get_total_num_statements())
        #     not_covered = [int(n) for n in G.all_stat - G.covered_stat]
        #     not_covered.sort()
        #     for n in not_covered:
        #         print(G.get_node_attr(str(n)))
        #     """

        #     npm_code_coveragr_logger.info("{}\t{}\t{}".format(package, len(G.covered_stat) / G.get_total_num_statements(), function_percentage))
            #if len(G.covered_stat) > G.get_total_num_statements():
            #    interesting = G.covered_stat - G.all_stat
            #    print(interesting)
            #    for item in interesting:
            #        print(G.is_statement(item))
                    #print(G.get_node_attr(item))
                #print(G.all_stat)
                #print(G.get_total_num_statements())
            #    return

        print('Detection result:', result)
        print('Exploit result:', exploit_result)
        if 1 in result:
            success_list.append(package)
            npm_success_logger.info("{} successfully found in {}".format(vul_type, package))
        elif len(result) == 0:
            npm_res_logger.error("Package json error in {}".format(package, result))
        elif all(v == 0 for v in result):
            npm_res_logger.error("Path not found in {}".format(package))
        elif -2 in result:
            not_found.append(package)
            npm_res_logger.error("Not found a file in {}".format(package))
        elif -3 in result:
            generate_error.append(package)
            npm_res_logger.error("Generate {} error".format(package))
        elif -4 in result:
            skip_list.append(package)
            npm_res_logger.error("Skip {}".format(package))
        else:
            npm_res_logger.error("Other problems {} return {}".format(package, result))

        detection = 'successful' if 1 in result else 'failed'
        if -1 in exploit_result:
            exploit = 'turned off'
        else:
            exploit = 'successful' if 1 in exploit_result else 'failed'
        npm_exploit_logger.info("{}, Detection: {}, Exploit: {}".format(package, detection, exploit))

        # del G

        if tgz_extract_path is not None and os.path.exists(tgz_extract_path):
            shutil.rmtree(tgz_extract_path)

    npm_test_logger.info("Success rate: {}%, {} out of {}, {} skipped and {} failed".format(float(len(success_list)) / total_cnt * 100,
            len(success_list), total_cnt, len(skip_list), total_cnt - len(skip_list) - len(success_list)))
    npm_test_logger.info("{} fails caused by package error, {} fails caused by generate error".format(len(not_found), len(generate_error)))
    npm_test_logger.info("Generation error list: {}".format(generate_error))

    print("Success rate: {}%, {} out of {}, {} skipped and {} failed".format(float(len(success_list)) / total_cnt * 100,
            len(success_list), total_cnt, len(skip_list), total_cnt - len(skip_list) - len(success_list)))

    print("{} fails caused by package error, {} fails caused by generate error".format(len(not_found), len(generate_error)))
