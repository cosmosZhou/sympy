from util.utility import user
from _collections import defaultdict
from util.search import py_to_module, read_directory, read_all_files,\
    yield_from_py, axiom_directory
from os.path import basename
from util import MySQL


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
        
#     sql = '''
#     CREATE TABLE `tbl_hierarchy_py` (
#       `user` varchar(32) NOT NULL,
#       `caller` varchar(256) NOT NULL,
#       `callee` varchar(256) NOT NULL,  
#       `count` int default 0,
#       PRIMARY KEY (`user`, `caller`, `callee`) 
#     ) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
#     PARTITION BY KEY () PARTITIONS 8;
#     '''
#     try:
#         MySQL.instance.execute(sql)
#     except Exception as e:
#         print(e)
#     
    MySQL.instance.execute('delete from tbl_hierarchy_py')
    
    MySQL.instance.load_data('tbl_hierarchy_py', data)

    
if __name__ == '__main__':
    insert_into_hierarchy()