import os, sys, re
from sympy.utilities.miscellany import Text
    
try: 
    import axiom  # @UnusedImport
except ImportError as e:
    from traceback import TracebackException
    etype, value, tb = sys.exc_info() 
    lines = [*TracebackException(type(value), value, tb, limit=None).format(chain=None)]
    error_source = lines[-2]
    
    print(error_source, file=sys.stderr)
    error_source = error_source.strip()
    error_message, line = error_source.splitlines()
    
    m = re.compile(r'File "([^"]+(?:\\|/)__init__\.py)", line (\d+), in <module>').fullmatch(error_message)
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
from os.path import getsize
from multiprocessing import cpu_count
from queue import PriorityQueue
from functools import singledispatch 
import random
from axiom.utility import RetCode
sep = os.path.sep


def axiom_directory(): 
    return os.path.dirname(axiom.__file__)


class Globals:
    count = 0

    @classmethod
    def increment_count(cls):
        cls.count += 1

    @classmethod
    def decrement_count(cls):
        cls.count -= 1

    unproved = []

    failures = []

    websites = []

    insurmountable = set()
    unprovable = set()


def readFolder(rootdir, sufix='.py'):
    for name in os.listdir(rootdir):
        path = os.path.join(rootdir, name)

        if path.endswith(sufix):
            name = name[:-len(sufix)]
            if name == '__init__':
                path = path[:-len(sufix) - len('/__init__')]
            else: 
                path = path[:-len(sufix)]
                
            paths = re.compile(r'[\\/]+').split(path)
#             print(path)
            index = paths.index('axiom')

            package = '.'.join(paths[index:])

            Globals.increment_count()
            path += '.php'            
            if os.path.isfile(path): 
                file = Text(path)
                line = file.readline()
                m = re.compile(r"<p style='display:none'>timing = ([\d.]+)</p>").match(line)
                if m:
                    timing = float(m.group(1))
                else:
                    timing = getsize(path) / 500
            else:
                timing = random.random()    
            
            yield package, timing

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
        m = re.compile('from \. import (\w+)((?:, *\w+)*)').match(line)
        if m:        
            if m.group(1) == module:
                hit = True
                break
            if m.group(2):
                if module in m.group(2).split(', *'):
                    hit = True
                    break                
    
    if not hit:
        addition = 'from . import '
        if delete:
            addition = ('del %s\n' % module) + addition
             
        addition += module
        
        last_char = file.get_last_char()
        if last_char and last_char != '\n':
            addition = '\n' + addition  
        file.append(addition)


def run(package): 
    command = 'python %s %s debug=True' % (project_directory() + sep + 'run.py', package)
    return os.system(command)
#     for line in os.popen(cmd).readlines():
#         print(line) 

    
def import_module(package):
    try: 
        return eval(package)
    except AttributeError as e: 
        print(e)
        s = str(e)
        
        m = re.compile("module '([\w\.]+)' has no attribute '(\w+)'").fullmatch(s)
        assert m 
        create_module(*m.groups())
        print(package, 'is created newly')
        return run(package)

        
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
        try:
            ret = module.prove(debug=debug)
            if package in Globals.insurmountable:
                ret = RetCode.insurmountable
        except AttributeError as e: 
            if os.path.basename(file) == '__init__.py':
                ret = RetCode.nonexistent
            else:
                print(file, 'is not a file of __init__.py!')
                raise e
                                
    except AttributeError as e:
        if isinstance(module, int):
            if module < 0:
                ret = RetCode.failure
            elif module:
                ret = RetCode.success
            else:
                ret = RetCode.plausible                
        else:
            print(module, 'from', module)
            print('importing errors found in', package)
            
            m = re.compile('(.*)\.(\w+)').match(package)
            create_module(*m.groups(), delete=True)
            ret = RetCode.failure
        
        file = project_directory() + sep + package.replace('.', sep) + '.py'        
            
    return package, file, ret


@process.register(list) 
def _(packages, debug=False):
    return [process(package, debug=debug) for package in packages]


start = time.time()    


def prove(debug=False, parallel=True): 
    
    def generator(): 
        rootdir = axiom_directory()
#         rootdir += r'\algebra\imply\le\abs'
        for name in os.listdir(rootdir):
            path = os.path.join(rootdir, name)
            
            if os.path.isdir(path):
                yield from readFolder(path)

    tasks = {task: timing for task, timing in generator()}
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
    
    for array in process(packages, debug=debug, parallel=parallel):
        post_process(array)
        
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
    for package, file, ret in result:
         
        if ret is RetCode.plausible: 
            Globals.unproved.append(file)
        elif ret is RetCode.failure:
            Globals.failures.append(file)
        elif ret is RetCode.nonexistent:
            Globals.decrement_count()
            continue
        elif ret is RetCode.insurmountable:
            continue
        else:
            continue
        
        Globals.websites.append("http://localhost/sympy/" + package.replace('.', sep) + ".php")
    return Globals.count


def process_debug(packages):
    return process(packages, debug=True)


@process.register(tuple) 
def _(items, debug=False, parallel=True):  # @DuplicatedSignature
    proc = process_debug if debug else process 
    if parallel: 
        from multiprocessing import Pool
        with Pool(processes=cpu_count()) as pool:
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
    for php in listdir(os.path.abspath(os.path.dirname(axiom.__file__))):
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

    debug = False
    parallel = True
    
    debug = kwargs.get('debug', debug)
    
    if not args:
#     prove(debug=True, parallel=False)    
#     prove(debug=True)
#     prove()
 
        prove(debug=debug, parallel=parallel)
    else: 

        def generator():
            for package in args:
                package = package.replace('/', '.').replace('\\', '.')
                module = import_module(package)
                if isinstance(module, int): 
                    ret = None if module < 0 else bool(module)
                    file = project_directory() + '/' + package.replace('.', '/') + '.py'        
                else:
                    file = module.__file__
                    ret = module.prove(debug=debug)                    
                yield package, file, ret
                
        post_process(generator())
        print_summary()
        
        if Globals.unproved: 
            exit_code = 0
        elif Globals.failures:
            exit_code = -1
        else:
            exit_code = 1
            
        print('exit_code =', exit_code)            
        exit(exit_code)
        
    if os.sep == '/':  # is Linux system
        cmd = 'chmod -R 777 axiom'
#         os.system(cmd)
        for s in os.popen(cmd).readlines():
            print(s)
                    
