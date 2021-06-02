import os
import regex as re
from sympy.utilities.miscellany import Text
from _collections import defaultdict


def axiom_directory():
    return os.path.dirname(__file__)


def read_directory(root):
    for name in os.listdir(root):
        path = os.path.join(root, name)
        if os.path.isdir(path):
            yield path


def read_all_php(root):
    for directory in read_directory(root):
        for php in read_all_files(directory, '.php'):
            yield php


def read_all_py(root):
    for directory in read_directory(root):
        for py in read_all_files(directory, '.py'):
            if os.path.basename(py) != '__init__.py': 
                yield py


def read_all_files(rootdir, sufix='.py'):
    for name in os.listdir(rootdir):
        path = os.path.join(rootdir, name)

        if path.endswith(sufix):
            yield path
        elif os.path.isdir(path):
            yield from read_all_files(path, sufix)


def print_py(axiom, prefix=os.path.dirname(axiom_directory())):
    path = prefix + '/' + axiom.replace('.', '/')
    py = path + '.py'
    if not os.path.exists(py):
        py = path + '/__init__.py'
    print(py)

    
def print_all_plausibles():
    plausible = defaultdict(list)
    read_all_plausibles(plausible)
    
    prefix = os.path.dirname(axiom_directory())
    print('axioms plausible:')
    for section in plausible:
        for axiom in plausible[section]:
            print_py(axiom, prefix)


def axiom_provability(module):
    return eval(module).prove.__name__
    
    
def read_all_plausibles(plausible):
    count = 0
    for php in read_all_php(os.path.dirname(__file__)):
        path = php[:-3]
        py = php[:-3] + 'py'
        
        if not os.path.exists(py):
            py = path + '/__init__.py'
        
        if not os.path.exists(py):
            print(php + " is an obsolete file since its py file is deleted!")
            os.unlink(php)
            continue
    
        count += 1
        if is_axiom_plausible(php): 
            axiom = py_to_module(php)
            
            provability = axiom_provability(axiom)
            if provability in ('insurmountable', 'unprovable'):
                continue
            
            sec = section(axiom)    
            plausible[sec].append(axiom)


def section(axiom):
    _, section, *_ = axiom.split('.', 3)
    return section


def is_axiom_plausible(php):
    for statement in yield_from_mysql(php):
        matches = is_latex(statement)
        for match in matches:
            if re.compile(".+tag\*\{(\?=.+)\}.+").search(match.group()):
                return True
            
    return False

    
def is_latex(latex): 
    return re.compile('\\\\\[.+?\\\\\]').finditer(latex)


def get_extension(file):
    return os.path.splitext(file)[-1]    

    
def py_to_module(py, delimiter='.'):
    module = []
    pythonFile = py
    while True:
        dirname = os.path.dirname(pythonFile)
        basename = os.path.basename(pythonFile)
        if basename == 'axiom':
            break
        
        module.append(basename)
        pythonFile = dirname

    module[0] = module[0][:-len(get_extension(module[0]))]
    
    module.reverse()

    if module[-1] == '__init__':
        module.pop()
    
    module = delimiter.join(module)
    return module


def yield_from_mysql(php):
    for statement in Text(php):
        if not statement.startswith(r"//"):
            continue

        statement = statement[2:]
        yield statement


def search(keyword, caseSensitive=True, wholeWord=False, regularExpression=False): 
    modules = []
    for php in read_all_py(os.path.dirname(__file__)):
        module = py_to_module(php)
#         print(module)
        if not caseSensitive:
            if wholeWord:
                if re.compile(r'\b%s\b' % keyword, re.I).search(module):
                    modules.append(module)
                    
            elif regularExpression:
                if re.compile(keyword, re.I).search(module):
                    modules.append(module)

            else:
                if keyword.tolower() in module.tolower():
                    modules.append(module)

        elif wholeWord:
            if re.compile(r'\b%s\b' % keyword).search(module):
                modules.append(module)
                
        elif regularExpression:
            if re.compile(keyword).search(module):
                modules.append(module)
        else:
            if keyword in module: 
                modules.append(module)
    
    prefix = os.path.dirname(axiom_directory())
    
    print("in all, there are %d hits:" % len(modules))
    for module in modules:
        print_py(module, prefix)
    
    
if __name__ == '__main__':
#     keyword = 'subs'

    keyword = ''
    caseSensitive = True
    wholeWord = False
    wholeWord = True    
    regularExpression = False
#     regularExpression = True
    
    if keyword:
        search(keyword, caseSensitive, wholeWord, regularExpression)
    else: 
        print_all_plausibles()
