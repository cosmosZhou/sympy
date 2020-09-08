# coding=utf-8
import os
import re
import axiom  # @UnusedImport
from sympy.utilities.misc import Text
import time
from os.path import getsize
from multiprocessing import cpu_count
from queue import PriorityQueue


count = 0

unproven = []

erroneous = []

websites = []

insurmountable = {'axiom.calculus.integral.intermediate_value_theorem',
                  'axiom.discrete.Fermat.LastTheorem',
                  'axiom.statistics.KullbackLeibler',
                  'axiom.trigonometry.cosine.theorem',
                  } 


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
            if package in insurmountable:
                continue                

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


def process_multiple(packages):
    return [process(package) for package in packages]

    
def process(package):
    try:    
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

        Text(__init__).append('from . import %s' % module)

        return dirname + sep + apply_package.replace('.', sep) + '.py', None
    file = package.__file__
    ret = package.prove(file)
    return file, ret

    
def prove():
    start = time.time()
    rootdir = os.path.dirname(__file__)
    
    def generator(): 
        for name in os.listdir(rootdir):
            path = os.path.join(rootdir, name)
            
            if os.path.isdir(path):
                yield from readFolder(path)

    tasks = {task : timing for task, timing in generator()}
    processes = []
    timings = []
    for _ in range(cpu_count() * 2):
        processes.append([])
        timings.append(0)
    
    total_timing = sum(timing for task, timing in tasks.items())
    
    average_timing = total_timing / len(processes)
    print('total_timing =', total_timing)
    print('average_timing =', average_timing)
    
    tasks = [*tasks.items()]
    tasks.sort(key=lambda pair : pair[1], reverse=True)
    
    pq = PriorityQueue()
    for i, t in enumerate(timings):
        pq.put((t, i))
        
    for task, timing in tasks:
        t, i = pq.get()
        processes[i].append(task)
        timings[i] += timing
        pq.put((timings[i], i))
        
    for proc, timing in zip(processes, timings):
        print(timing, proc)
        
    print('total timing =', sum(timings))
    
    for array in parellel_process(process_multiple, processes):
        for package, ret in array: 
            if ret is False:                
                unproven.append(package)
            elif ret is None:
                erroneous.append(package)
            else:
                continue
            websites.append("http://localhost" + package[len(os.path.dirname(os.path.dirname(os.path.dirname(__file__)))):-3] + ".php")

    print('in all %d axioms' % count)

    if unproven:
        print('unproven axioms')
        for p in unproven:
            print(p)

    if erroneous:
        print('erroneous axioms')
        for p in erroneous:
            print(p)

    if websites :
        print('.php websites')
        for p in websites:
            print(p)
    timing = time.time() - start
    print('cost time =', timing / 60, 'minutes =', timing, 'seconds')
    print('total unprovable =', len(unproven))
    print('total erroneous =', len(erroneous))
    
def parellel_process(process, items):
#     return map(process, items)
    from multiprocessing import Pool
    with Pool(processes=cpu_count() * 2) as pool:
        return pool.map(process, items)

       
if __name__ == '__main__':    
    prove()
    
# Reverse[Reverse[Minors[mat], 1], 2] == Map[Reverse, Minors[mat], {0, 1}]

# adj[m_] := Map[Reverse, Minors[Transpose[m], Length[m] - 1], {0, 1}] Table[(-1)^(i + j), {i, Length[m]}, {j, Length[m]}]
# $Assumptions = M \[Element] Matrices[{n, n}, Reals, Symmetric[{1, 2}]]
# Normal[SparseArray[{{i_, i_} -> i^2}, {10, 10}]] // MatrixForm
