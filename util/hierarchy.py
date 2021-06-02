from axiom.utility import user
from _collections import defaultdict
from axiom.search import py_to_module, read_directory, read_all_files
from os.path import dirname, basename
from axiom import MySQL


def read_all_axioms(dir):

    for directory in read_directory(dir):
        for py in read_all_files(directory, 'py'):
            if basename(py) != "__init__.py":
                yield py, py[0:-2] + 'php'

            else:
                yield py, py[0:-len('/__init__.py')] + '.php'


# input is a py file
def detect_dependency_from_py(py):

    axioms = []

    for dict in yield_from_py(py):
        print(dict)

        if 'a' in dict:
            for index, axiom in dict['a'].items():
                axioms.append(axiom)
    return axioms


def retrieve_all_dependency():

    for py, php in read_all_axioms(dirname(__file__)):
        source = py_to_module(php)

        count = defaultdict(int)
        for to in detect_dependency_from_py(py):
            count[to] += 1

        yield source, count


if __name__ == '__main__':
    data = []
    for caller, counts in retrieve_all_dependency(): 
        for callee, count in counts.items():
            args = user, caller, callee, count
            data.append(args);
        
    sql = '''
    CREATE TABLE `tbl_hierarchy_py` (
      `user` varchar(32) NOT NULL,
      `caller` varchar(256) NOT NULL,
      `callee` varchar(256) NOT NULL,  
      `count` int default 0,
      PRIMARY KEY (`user`, `caller`, `callee`) 
    ) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
    PARTITION BY KEY () PARTITIONS 8;
    '''
    try:
        MySQL.instance.execute(sql)
    except Exception as e:
        print(e)
    
    MySQL.instance.load_data('tbl_hierarchy_py', data)

