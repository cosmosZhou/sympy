from util.utility import user
from _collections import defaultdict
from util.search import py_to_module, read_directory, read_all_files,\
    yield_from_py, axiom_directory, is_py_theorem
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
        source = py_to_module(php)

        count = defaultdict(int)        
        if is_py_theorem(py):
            print("py =", py)
            for to in yield_from_py(py):
                count[to] += 1

            yield source, count


def insert_into_hierarchy():
    data = []
    for caller, counts in retrieve_all_dependency():         
        for callee, count in counts.items():
#             print(user, caller, callee, count)
            args = user, caller, callee, count
            data.append(args)
        
    MySQL.instance.execute('delete from tbl_hierarchy_py')
    
    MySQL.instance.load_data('tbl_hierarchy_py', data)

    
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

#from util.hierarchy import update_timestamp
#update_timestamp()
if __name__ == '__main__':
    insert_into_hierarchy()
#     update_timestamp()    

#exec(open('./util/hierarchy.py').read())