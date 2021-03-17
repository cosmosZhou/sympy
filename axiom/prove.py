import os
import re
import axiom  # @UnusedImport
from sympy.utilities.miscellany import Text
import time
from os.path import getsize
from multiprocessing import cpu_count
from queue import PriorityQueue
from functools import singledispatch 
import random
from axiom.utility import RetCode


def axiom_directory():
    return os.path.dirname(__file__)


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
                with open(path, "r", encoding='utf8') as file:
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


def create_module(package, module):
    sep = os.path.sep
    dirname = project_directory()
    __init__ = dirname + sep + package.replace('.', sep) + sep + '__init__.py'
    print('editing', __init__)
    
    hit = False
    file = Text(__init__)
    for line in file:
        m = re.compile('from \. import (\w+)').match(line)        
        if m and m.group(1) == module:
            hit = True
            break
        
    if not hit:
        addition = 'from . import %s' % module
        last_char = file.get_last_char()
        if last_char and last_char != '\n':
            addition = '\n' + addition  
        file.append(addition)


def run(package): 
    command = 'python %s %s debug=True' % (project_directory() + os.path.sep + 'run.py', package)
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
    if debug:
        print(package)
        
    module = import_module(package)
    if isinstance(module, int):
        sep = os.path.sep
        
        if module < 0:
            ret = RetCode.failure
        elif module:
            ret = RetCode.success
        else:
            ret = RetCode.plausible
            
        file = project_directory() + sep + package.replace('.', sep) + '.py'
    else: 
        file = module.__file__
        if hasattr(module, 'prove'):
            ret = module.prove(file, debug=debug)
            if package in insurmountable:
                ret = RetCode.insurmountable
        else:
            ret = RetCode.nonexistent
            
    return file, ret


@process.register(list) 
def _(packages, debug=False):
    return [process(package, debug=debug) for package in packages]


start = time.time()    


def prove(debug=False, parallel=True):
    rootdir = axiom_directory()
    
    def generator(): 
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
    
#     tasks = {'axiom.calculus.is_continuous.is_differentiable.eq.imply.exists_eq.Rolle': 0}
    
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
    if unproved:
        print('unproved:')
        for p in unproved:
            print(p)

    if failures:
        print('failures:')
        for p in failures:
            print(p)

    if websites:
        print('websites:')
        for p in websites:
            print(p)
    timing = time.time() - start
    print('seconds costed =', timing)
    print('minutes costed =', timing / 60)    
    print('total unproved =', len(unproved))
    print('total failures =', len(failures))

        
def post_process(result):
    for package, ret in result: 
        if ret is RetCode.plausible: 
            unproved.append(package)
        elif ret is RetCode.failure:
            failures.append(package)
        elif ret is RetCode.nonexistent:
            Globals.decrement_count()
            continue
        elif ret is RetCode.insurmountable:
            continue
        else:
            continue
        
#         print('__file__ =', __file__)
#         print('working_directory() =', working_directory())
#         print('package =', package)
        
        websites.append("http://localhost" + package[len(working_directory()):-3] + ".php")
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


if __name__ == '__main__':
#     prove(debug=True, parallel=False)    
#     prove(debug=True)
    prove()
    
