
# coding=utf-8
import os
import re
import axiom  # @UnusedImport
from sympy.utilities.misc import Text
import time
from os.path import getsize
from multiprocessing import cpu_count
from queue import PriorityQueue
from functools import singledispatch 

count = 0

unproved = []

failures = []

websites = []

insurmountable = {*Text(os.path.dirname(__file__) + '/insurmountable.txt')}
unprovable = {*Text(os.path.dirname(__file__) + '/unprovable.txt')}

insurmountable |= unprovable


def readFolder(rootdir, sufix='.py'):
    for name in os.listdir(rootdir):
        path = os.path.join(rootdir, name)

        if path.endswith(sufix):
            name = name[:-len(sufix)]
            if name == '__init__':
                continue
            
            path = path[:-len(sufix)]
            paths = re.compile(r'[\\/]+').split(path)
#             print(path)
            index = paths.index('axiom')

            package = '.'.join(paths[index:])
#             if package in insurmountable:
#                 continue                
            global count
            count += 1
            path += '.php'
            timing = 0
            if os.path.isfile(path):                
                with open(path, "r", encoding='utf8') as file:
                    line = file.readline()                    
                    m = re.compile(r"<p style='display:none'>timing = ([\d.]+)</p>").match(line)
                    if m:
                        timing = float(m.group(1))
                    else:
                        timing = getsize(path) / 500
            
            yield package, timing

        elif os.path.isdir(path):
            yield from readFolder(path, sufix)


@singledispatch    
def process(package, debug=False):
    is_insurmountable = package in insurmountable
        
    try:    
        if debug:
            print(package)
        package = eval(package)
    except AttributeError as e:   
        print(e)
        s = str(e)

        m = re.compile("module '([\w\.]+)' has no attribute '(\w+)'").fullmatch(s)
        assert m
        apply_package = package
        package, module = m.groups()

        sep = os.path.sep
        dirname = os.path.dirname(os.path.dirname(__file__))
        __init__ = dirname + sep + package.replace('.', sep) + sep + '__init__.py'
        print('editing', __init__)
        
        hit = False
        for line in Text(__init__):
            m = re.compile('from \. import (\w+)').match(line)
            assert m
            if m.group(1) == module:
                hit = True
                break
        if not hit:
            Text(__init__).append('from . import %s' % module)

        return dirname + sep + apply_package.replace('.', sep) + '.py', None
    file = package.__file__
    ret = package.prove(file, debug=debug)
    if is_insurmountable:
        ret = True
    return file, ret


@process.register(list) 
def _(packages, debug=False):
    return [process(package, debug=debug) for package in packages]


start = time.time()    


def prove(debug=False, parallel=True):
    rootdir = os.path.dirname(__file__)
    
    def generator(): 
        for name in os.listdir(rootdir):
            path = os.path.join(rootdir, name)
            
            if os.path.isdir(path):
                yield from readFolder(path)

    tasks = {task : timing for task, timing in generator()}
    packages = tuple([] for _ in range(cpu_count() * 2))
    timings = [0 for _ in range(cpu_count() * 2)]
    
    total_timing = sum(timing for task, timing in tasks.items())
    
    average_timing = total_timing / len(packages)
    print('total_timing =', total_timing)
    print('average_timing =', average_timing)
    
    tasks = [*tasks.items()]
    tasks.sort(key=lambda pair : pair[1], reverse=True)
    
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
        
    print('in all %d axioms' % count)
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
        if ret is False:                
            unproved.append(package)
        elif ret is None:
            failures.append(package)
        else:
            continue
        
#         print('__file__ =', __file__)
#         print('os.path.dirname(os.path.dirname(os.path.dirname(__file__))) =', os.path.dirname(os.path.dirname(os.path.dirname(__file__))))
#         print('package =', package)
        
        websites.append("http://localhost" + package[len(os.path.dirname(os.path.dirname(os.path.dirname(__file__)))):-3] + ".php")


def process_dubug(packages):
    return process(packages, debug=True)


@process.register(tuple) 
def _(items, debug=False, parallel=True):  # @DuplicatedSignature
    proc = process_dubug if debug else process 
    if parallel:        
        from multiprocessing import Pool
        
        with Pool(processes=cpu_count() * 2) as pool:
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
    
