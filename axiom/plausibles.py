# coding=utf-8
import os
import re
from sympy.utilities.miscellany import Text
from _collections import defaultdict


def axiom_directory():
    return os.path.dirname(__file__)


def read_directory(dir):
    for name in os.listdir(dir):
        path = os.path.join(dir, name)
        if os.path.isdir(path):
            yield path


def read_all_php(dir):
    for directory in read_directory(dir):
        for php in read_all_files(directory, '.php'):
            yield php


def read_all_files(rootdir, sufix='.py'):
    for name in os.listdir(rootdir):
        path = os.path.join(rootdir, name)

        if path.endswith(sufix):
            yield path
        elif os.path.isdir(path):
            yield from read_all_files(path, sufix)


def read_all_plausibles(plausible):
    count = 0
    for php in read_all_php(os.path.dirname(__file__)):
        py = php[:-3] + 'py'
        if not os.path.exists(py):
            print(php + " is an obsolete file since its py file is deleted!")
            os.unlink(php)
            continue        
    
        count += 1
        if is_axiom_plausible(php):
            axiom = to_python_module(php)
    
            sec = section(axiom)
            if sec in insurmountable:
                if axiom in insurmountable[sec]:
                    continue
    
            if sec in unprovable:
                if axiom in unprovable[sec]:
                    continue
    
            plausible[sec].append(axiom)


def section(axiom):
    _, section, *_ = axiom.split('.', 3)
    return section


def is_axiom_plausible(php):
    for statement in yield_from_php(php):
        matches = is_latex(statement)
        for match in matches:
            if re.compile(".+tag\*\{(.+=>.+)\}.+").search(match.group()):
                return True
            
    return False

    
def is_latex(latex): 
    return re.compile('\\\\\[.+?\\\\\]').finditer(latex)

    
sagemath = os.path.basename(os.path.dirname(os.path.dirname(__file__)))

insurmountable = defaultdict(list) 

for axiom in Text(axiom_directory() + '/insurmountable.txt'):
    insurmountable[section(axiom)].append(axiom)

unprovable = defaultdict(list)
for axiom in Text(axiom_directory() + '/unprovable.txt'):
    unprovable[section(axiom)].append(axiom)

    
def get_extension(file):
    return os.path.splitext(file)[-1]    

    
def to_python_module(py):
    global sagemath
    module = []
    pythonFile = py
    while True:
        dirname = os.path.dirname(pythonFile)
        basename = os.path.basename(pythonFile)
        if basename == sagemath:
            break
        
        module.append(basename)
        pythonFile = dirname

    module[0] = module[0][:-len(get_extension(module[0]))]
    module.reverse()

    module = '.'.join(module)
    return module


def yield_from_php(php):
    for statement in Text(php):
        if not statement.startswith(r"//"):
            continue

        statement = statement[2:]
        yield statement


if __name__ == '__main__':
    plausible = defaultdict(list)
    read_all_plausibles(plausible)
    
    prefix = os.path.dirname(axiom_directory())
    print('axioms plausible:')
    for section in plausible:
        for axiom in plausible[section]:
            print(prefix + '/' + axiom.replace('.', '/') + '.py')
    
