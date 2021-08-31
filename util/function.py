from util.utility import user
from util.search import py_to_module, read_directory, read_all_files, \
    axiom_directory, is_py_theorem, yield_function_from_py
from os.path import basename
from util import MySQL
import time
import datetime


def read_all_axioms(dir):

    for directory in read_directory(dir):
        print(directory)
        for py in read_all_files(directory, '.py'):
            if basename(py) != "__init__.py":
                yield py, py[0:-2] + 'php'
            else:
                yield py, py[0:-len('/__init__.py')] + '.php'


def retrieve_all_dependency(): 
    print("axiom_directory =", axiom_directory())
    for py, php in read_all_axioms(axiom_directory()):
        caller = py_to_module(php)
        if is_py_theorem(py):
            dic = {callee: func for callee, func in yield_function_from_py(py)}
            if dic:
                print("py =", py)  
                yield caller, dic 


def insert_into_function():
    data = []
    for caller, funcs in retrieve_all_dependency(): 
        for callee, func in funcs.items():
            print(user, caller, callee, func)
            args = user, caller, callee, func
            data.append(args)
        
    MySQL.instance.execute('delete from tbl_function_py')
    
    MySQL.instance.load_data('tbl_function_py', data)

    
def topological_sort():
    graph = {}
    axiomSet = set()
    for caller, counts in retrieve_all_dependency(): 
        for callee, count in counts.items():
            if caller not in graph:
                graph[caller] = []
            # caller is dependent on callee, so callee is a parent of caller
            graph[caller].append(callee)                        
            axiomSet.add(callee)
        axiomSet.add(caller)
        
    axiomSet -= graph.keys()
    if axiomSet:
        for axiom in axiomSet:
            graph[axiom] = []
             
    from sympy.utilities.iterables import topological_sort_depth_first
    
    G = topological_sort_depth_first(graph)
    return G

    
def update_timestamp():
    G = topological_sort()
    # for axiom in G:
        # print(axiom)

    print(len(G))
    datetime.date(2018, 1, 1)
    initial = time.mktime(datetime.date(2018, 1, 1).timetuple())
    delta = time.time() - initial
    delta /= len(G)
    
    create_times = []
    for i in range(len(G)):
        create_time = initial + delta * i
        create_time = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(create_time))
        create_times.append(create_time)
        
    seq_params = [(create_time, axiom) for axiom, create_time in zip(G, create_times)]
        
    print("len(seq_params) =", len(seq_params))
    rowcount = MySQL.instance.executemany("update tbl_axiom_py set timestamp = %s where user = 'sympy' and axiom = %s", seq_params)
    print("rowcount =", rowcount)


if __name__ == '__main__':
    insert_into_function()
#     update_timestamp()    
# exec(open('./util/function.py').read())