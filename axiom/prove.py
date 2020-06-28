import os
import re
import axiom
from sympy.utilities.misc import Text
import time

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
            
            path = re.compile(r'[\\/]+').split(path[:-len(sufix)])
#             print(path)
            index = path.index('axiom')

            package = '.'.join(path[index:])
            try:
#                 package = eval(package)
                if package in insurmountable:
                    continue                
            except AttributeError as e:
                print(e)
                s = str(e)

                m = re.compile("module '([\w\.]+)' has no attribute '(\w+)'").fullmatch(s)
                assert m
                package, module = m.groups()

                __init__ = '/'.join(path[:index]) + '/' + package.replace('.', '/') + '/__init__.py'
                print('editing', __init__)

                Text(__init__).append('from . import %s' % module)
                continue

            global count
            count += 1
            yield package

        elif os.path.isdir(path):
            yield from readFolder(path, sufix)


def process(package):
    print('testing', package)    
    package = eval(package)
    file = package.__file__
    return file, package.prove(file)

    
def prove():
    start = time.time()
    rootdir = os.path.dirname(__file__)
    
    def generator(): 
        for name in os.listdir(rootdir):
            path = os.path.join(rootdir, name)
            
            if os.path.isdir(path):
                yield from readFolder(path)
                
#     for package, ret in map(process, [*generator()]):
    for package, ret in parellel_process(process, [*generator()]):
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
    print('cost time =', (time.time() - start) / 60, 'minutes')


def parellel_process(process, items):
    from multiprocessing import Pool
    from multiprocessing import cpu_count
    pool = Pool(processes=cpu_count() * 2)
    results = pool.map(process, items)
    pool.close()
    pool.join()
    return results

    
if __name__ == '__main__':    
    prove()
    
