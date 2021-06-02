import os, sys, re
from sympy.utilities.miscellany import Text

try:
    import axiom
except ImportError as e:
    from traceback import TracebackException
    etype, value, tb = sys.exc_info() 
    lines = [*TracebackException(type(value), value, tb, limit=None).format(chain=None)]
    error_source = lines[-2]

    print(error_source, file=sys.stderr)
    error_source = error_source.strip()
    error_message, line = error_source.splitlines()

    m = re.fullmatch(r'File "([^"]+(?:\\|/)__init__\.py)", line (\d+), in <module>', error_message)
    assert m
    file, line_number = m.groups()

    line_number = int(line_number) - 1
    print('file =', file)
    print('line_number =', line_number)

    file = Text(file)

    lines = file.readlines()    
    del lines[line_number]

    file.writelines(lines)

    command = 'python ' + ' '.join(sys.argv)
    print(command)

    exit_code = os.system(command)
    print('exit_code =', exit_code)
    exit(exit_code)

import time
from multiprocessing import cpu_count
from queue import PriorityQueue
from functools import singledispatch 
import random
from util.utility import RetCode
sep = os.path.sep


def axiom_directory():
    directory = os.path.dirname(__file__)
    if not directory:
        return './axiom'
    return directory + '/axiom'


class Globals:
    count = 0

    @classmethod
    def increment_count(cls):
        cls.count += 1

    unproved = []

    failures = []

    websites = []

    data = []


def readFolder(rootdir, sufix='.py'):
    for name in os.listdir(rootdir):
        path = os.path.join(rootdir, name)

        if path.endswith(sufix):
            name = name[:-len(sufix)]
            if name == '__init__':
                line = Text(path).readline()                
                if not line:
                    lines = Text(path).readlines()
                    for i, line in enumerate(lines):
                        if line:
                            break
                    
                    try:
                        lines = lines[i:]
                        Text(path).writelines(lines)
                    except UnboundLocalError:
                        print(f'removing empty {path}')
                        os.remove(path)
                        continue                    
                    
                if re.match('from *\. *import +\w+', line):
                    continue

                path = path[:-len(sufix) - len('/__init__')]                
            else: 
                path = path[:-len(sufix)]

            paths = re.split(r'[\\/]+', path)
#             print(path)
            index = paths.index('axiom')

            package = '.'.join(paths[index + 1:])

            Globals.increment_count()
            
            yield package

        elif os.path.isdir(path):
            yield from readFolder(path, sufix)


def project_directory():
    return os.path.dirname(axiom_directory())


def working_directory():
    return os.path.dirname(project_directory())


def create_module(package, module, delete=False):
    print('package =', package)
    print('module =', module)
    
    dirname = project_directory()
    __init__ = dirname + sep + package.replace('.', sep) + sep + '__init__.py'
    print('editing', __init__)
    
    hit = False
    
    file = Text(__init__)
    
    for line in file:
        m = re.match('from \. import (\w+(?:, *\w+)*)', line)
        if m and module in m.group(1).split(', *'):
            hit = True
            break                
    
    if not hit:
        addition = 'from . import '
        if delete:
            addition = ('del %s\n' % module) + addition
             
        addition += module
        
        if len(file) and not file.endswith('\n'):
            addition = '\n' + addition  
        file.append(addition)


def run(package, debug=True):
    args = (project_directory() + sep + 'run.py', package)
    if debug:
        return os.system('python %s %s debug=True' % args)
    else: 
        return os.popen('python %s %s' % args).readlines() 

    
def import_module(package, debug=False):
    try: 
        module = axiom
        for attr in package.split('.'):
            module = getattr(module, attr)
        return module
    
    except AttributeError as e: 
        print(e)
        s = str(e)
        
        m = re.fullmatch("module '([\w\.]+)' has no attribute '(\w+)'", s)
        assert m 
        create_module(*m.groups())
        print(package, 'is created newly')
        return run(package, debug=debug)


def prove_with_timing(module, debug):
    lapse = time.time()
    state, latex = module.prove(debug=debug)
    lapse = time.time() - lapse
    return state, lapse, latex            


def interpret_int_from_import(module):
    if module < 0:
        return RetCode.failure
    elif module:
        return RetCode.success
    else:
        return RetCode.plausible    


@singledispatch    
def process(package, debug=False):
    module = import_module(package)    
#     https://www.geeksforgeeks.org/try-except-vs-if-in-python/
# We often hear that python always encourages EAFP(
# “It’s easier to ask for forgiveness than permission”) 
# style over LBYL ( “Look before you leap ” ) style used in most of the languages like C.
    try: 
        file = module.__file__
        if debug:
            print(file)
            
        state, lapse, latex = prove_with_timing(module, debug)
                                
    except AttributeError as e:
        lapse = None
        latex = None 
        if isinstance(module, int):
            state = interpret_int_from_import(module)
        else:
            print(module, 'from', module)
            print('importing errors found in', package)

            m = re.match('(.*)\.(\w+)', package)
            _package, module = m.groups()
            _package = 'axiom.' + _package
            create_module(_package, module, delete=True)
            state = RetCode.failure
        
        file = project_directory() + sep + package.replace('.', sep) + '.py'        
            
    return package, file, state, lapse, latex


@process.register(list) 
def _(packages, debug=False):
    return [process(package, debug=debug) for package in packages]


start = time.time()    

user = os.path.basename(os.path.dirname(os.path.realpath(__file__)))
assert user, 'user should not be empty!'

def prove(debug=False, parallel=True): 
    from util import MySQL
    def generator(): 
        rootdir = axiom_directory()
#         rootdir += r'\algebra\imply\le\abs'
        for name in os.listdir(rootdir):
            path = os.path.join(rootdir, name)
            
            if os.path.isdir(path):
                yield from readFolder(path)

    taskSet = {*generator()}
    
#     taskSet = {*[*taskSet][:100]}

    tasks = MySQL.select_axiom_lapse_from_tbl_axiom_py(user=user)
    deleteSet = tasks.keys() - taskSet
    if len(deleteSet) > 1:
        MySQL.instance.execute("delete from tbl_axiom_py where user='%s' and axiom in %s" % (user, tuple(deleteSet)))
    elif len(deleteSet) == 1:
        deleteAxiom, *_ = deleteSet
        MySQL.instance.execute("delete from tbl_axiom_py where user='%s' and axiom = '%s'" % (user, deleteAxiom))
        
    for key in deleteSet:
        del tasks[key]
    
    for module in taskSet - tasks.keys():
        tasks[module] = random.random()
        
    packages = tuple([] for _ in range(cpu_count() * 2))
    timings = [0 for _ in range(cpu_count() * 2)]
    
    total_timing = sum(timing for task, timing in tasks.items())
    
    average_timing = total_timing / len(packages)
    print('total_timing =', total_timing)
    print('average_timing =', average_timing)
    
    tasks = [*tasks.items()]
    tasks.sort(key=lambda pair: pair[1], reverse=True)
    
    pq = PriorityQueue()
    for i, t in enumerate(timings):
        pq.put((t, i))
        
    for task, timing in tasks:
        t, i = pq.get()
        packages[i].append(task)
        timings[i] += timing
        pq.put((timings[i], i))
        
    for proc, timing in zip(packages, timings):
        print('timing =', timing)
        print('python run.py ' + ' '.join(proc))
        
    print('total timing =', sum(timings))
    
    data = []
    for array in process(packages, debug=debug, parallel=parallel):
        data += post_process(array)
        
    MySQL.instance.load_data('tbl_axiom_py', data, replace=True)
    print('in all %d axioms' % Globals.count)
    print_summary()

    
def print_summary():
    if Globals.unproved:
        print('unproved:')
        for p in Globals.unproved:
            print(p)

    if Globals.failures:
        print('failures:')
        for p in Globals.failures:
            print(p)

    if Globals.websites:
        print('websites:')
        for p in Globals.websites:
            print(p)
    timing = time.time() - start
    print('seconds costed =', timing)
    print('minutes costed =', timing / 60)    
    print('total unproved =', len(Globals.unproved))
    print('total failures =', len(Globals.failures))

        
def post_process(result):
    data = []
    for package, file, state, lapse, latex in result:
        
        data.append((user, package, state, lapse, latex))
            
        if state is RetCode.plausible: 
            Globals.unproved.append(file)
        elif state is RetCode.failure:
            Globals.failures.append(file)
        else:
            continue
        
        Globals.websites.append("http://localhost/sympy/axiom.php/" + package.replace('.', '/'))
        
    return data


def process_debug(packages):
    return process(packages, debug=True)


@process.register(tuple) 
def _(items, debug=False, parallel=True):  # @DuplicatedSignature
    proc = process_debug if debug else process 
    if parallel: 
        from multiprocessing import Pool
        processes = cpu_count()
        with Pool(processes=processes) as pool:
#         with Pool(processes=cpu_count() * 2) as pool:
            return pool.map(proc, items)
    else:
        return map(proc, items)
       
# Reverse[Reverse[Minors[mat], 1], 2] == Map[Reverse, Minors[mat], {0, 1}]

# adj[m_] := Map[Reverse, Minors[Transpose[m], Length[m] - 1], {0, 1}] Table[(-1)^(i + j), {i, Length[m]}, {j, Length[m]}]

# to create a matrix symbol 
# $Assumptions = M \[Element] Matrices[{n, n}, Reals, Symmetric[{1, 2}]]
# Normal[SparseArray[{{i_, i_} -> i^2}, {10, 10}]] // MatrixForm


def listdir(rootdir, sufix='.php'):
    for name in os.listdir(rootdir):
        path = os.path.join(rootdir, name)

#         if path.endswith(sufix):
#             yield path
        if os.path.isdir(path):
            yield from listdir_recursive(path, sufix)


def listdir_recursive(rootdir, sufix='.php'):
    for name in os.listdir(rootdir):
        path = os.path.join(rootdir, name)

        if path.endswith(sufix):
            yield path
        elif os.path.isdir(path):
            yield from listdir_recursive(path, sufix)


def clean(): 
    for php in listdir(os.path.abspath(axiom_directory())):
        py = php.replace('.php', '.py')
        if not os.path.exists(py):
            print(php)
            os.remove(php)

    
def args_kwargs(argv):
    args = []
    kwargs = {}
    for arg in argv:
        arr = arg.split('=')
        if len(arr) == 2:
            key, value = arr
            kwargs[key] = eval(value)
        else:
            args.append(arg)
    return args, kwargs


if __name__ == '__main__':
    args, kwargs = args_kwargs(sys.argv[1:])
    if kwargs:
        if 'clean' in kwargs:
            clean()

    debug = kwargs.get('debug', False)
    parallel = kwargs.get('parallel', True)
    if not args:
        prove(debug=debug, parallel=parallel)
    else: 

        def generator():
            for package in args:
                package = package.replace('/', '.').replace('\\', '.')
                module = import_module(package)
                if isinstance(module, int):
                    state = interpret_int_from_import(module)                    
                    file = project_directory() + '/' + package.replace('.', '/') + '.py'
                    lapse = None
                    latex = None         
                else:
                    file = module.__file__
                    try:
                        state, lapse, latex = prove_with_timing(module, debug)
                    except AttributeError:
                        continue
                    
                yield package, file, state, lapse, latex                        
                
        data = post_process(generator())
        import tempfile, uuid 
        sql = "%s/%s.sql" % (tempfile.gettempdir(), uuid.uuid4())        
        assert not os.path.exists(sql)
        print("latex results are saved into:")
        print(sql)
        
        sql = Text(sql)
#         sql.clear()
        file = sql.file
        
        from util.MySQL import json_encode
        for args in data: 
            _args = []
            for arg in args:
                if not isinstance(arg, str):
                    arg = str(arg)
                    
                _args.append(json_encode(arg))
            
            print("replace into tbl_axiom_py values(%s);" % ','.join(_args), file=file)
        
        print_summary()
        
        if Globals.unproved: 
            exit_code = 0
        elif Globals.failures:
            exit_code = -1
        else:
            exit_code = 1
            
        print('exit_code =', exit_code)
        exit(exit_code)
        
    from util.utility import chmod
    chmod()
                    
