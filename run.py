#!/usr/local/python3/bin/python3
#!/home/lizhi/python/bin/python

import os, sys, re
from sympy.utilities.misc import Text

try:
    import axiom
except ImportError as e:
    from util.utility import source_error
    error_message, line = source_error()

    m = re.fullmatch(r'File "([^"]+(?:\\|/)__init__\.py)", line (\d+), in <module>', error_message)
    assert m, error_message
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

    plausible = []

    failed = []

    data = []
    

def readFolder(rootdir, sufix='.py'):
    names = os.listdir(rootdir)
    unused = 0
    for name in names:
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
                    else:
                        i = len(lines)
                        
                    if not i:
                        try:
                            os.remove(path)
                        except PermissionError as e:
                            print(e)                            
                        continue
 
                    try:
                        lines = lines[i:]
                        Text(path).writelines(lines)
                    except UnboundLocalError:
                        print(f'removing {path}')                        
                        try:
                            os.remove(path)
                        except PermissionError as e:
                            print(e)
                            
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
            if name == '__pycache__':
                unused += 1
            else:
                yield from readFolder(path, sufix)
        else:
            unused += 1

    if unused == len(names):
        print(f"removing empty directory {rootdir}")
        import shutil
        shutil.rmtree(rootdir)                
            

def project_directory():
    return os.path.dirname(axiom_directory())


def working_directory():
    return os.path.dirname(project_directory())


def create_module(package, module):
    print('package =', package)
    print('module =', module)
    
    dirname = project_directory()
    __init__ = dirname + sep + package.replace('.', sep) + sep + '__init__.py'
    print('editing', __init__)
    
    hit = False
    
    file = Text(__init__)
    
    for line in file:
        m = re.match('from \. import (\w+(?:, *\w+)*)', line)
        if m and module in m[1].split(', *'):
            hit = True
            break                
    
    if not hit:
        addition = 'from . import '
        addition += module
        
        if file.size and not file.endswith('\n'):
            addition = '\n' + addition  
        file.append(addition)


def run(package, debug=True):
    args = (project_directory() + sep + 'run.py', package)
    if debug:
        return os.system('python %s %s debug=True' % args)
    else: 
        try:
            return os.popen('python %s %s' % args).readlines()
        except UnicodeDecodeError as e:
            print(e)

    
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


def prove_with_timing(module, **kwargs):
    lapse = time.time()
    state, latex = module.prove(**kwargs)
    lapse = time.time() - lapse    
    return state, lapse, latex            


def interpret_int_from_import(module):
    if module < 0:
        return RetCode.failed
    elif module:
        return RetCode.proved
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
            
        state, lapse, latex = prove_with_timing(module, debug=debug)
                                
    except AttributeError as e:
        lapse = None
        latex = None 
        if isinstance(module, int):
            state = interpret_int_from_import(module)
        else:
            print(module, 'from', module)
            print(e)
            print('importing errors found in', package)

            m = re.match('(.*)\.(\w+)', package)
            _package, module = m.groups()
            _package = 'axiom.' + _package
            create_module(_package, module)
            state = RetCode.failed
        
        file = project_directory() + sep + package.replace('.', sep) + '.py'        
            
    return package, file, state, lapse, latex


@process.register(list) 
def _(packages, debug=False):
    return [process(package, debug=debug) for package in packages]


start = time.time()    

user = os.path.basename(os.path.dirname(os.path.realpath(__file__)))
assert user, 'user should not be empty!'

def prove(**kwargs): 
    from util import MySQL

    def generator(): 
        rootdir = axiom_directory()
#         rootdir += r'\algebra\imply\le\abs'
        for name in os.listdir(rootdir):
            path = os.path.join(rootdir, name)
            
            if os.path.isdir(path):
                if name != '__pycache__':
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
    
    newTasks = taskSet - tasks.keys()
    if newTasks:
        for i, module in enumerate(newTasks):
            tasks[module] = random.random()

    packages = tuple([] for _ in range(cpu_count()))
    timings = [0 for _ in range(cpu_count())]
    
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
    
    for array in process(packages, **kwargs):
        data += post_process(array, True)
        
    MySQL.instance.load_data('tbl_axiom_py', data, replace=True, ignore=True)
    print('in all %d axioms' % Globals.count)
    print_summary()

    
def print_summary():
    if Globals.plausible:
        print('plausible:')
        for p in Globals.plausible:
            for p in p:
                print(p)
            print()
            
    if Globals.failed:
        print('failed:')
        for p in Globals.failed:
            for p in p:
                print(p)
            print()

    timing = time.time() - start
    print('seconds costed =', timing)
    print('minutes costed =', timing / 60)    
    print('total plausible =', len(Globals.plausible))
    print('total failed    =', len(Globals.failed))

        
def post_process(result, truncate=False):
    data = []
    for package, file, state, lapse, latex in result:
        if latex is None:
            print(package)
            print(file)
            latex = ''
            assert state is RetCode.failed
        if truncate and len(latex) > 65535:
            latex = latex[:65535]
            
        data.append((user, package, state, lapse, latex))
            
        if state is RetCode.plausible: 
            Globals.plausible.append((file, f"http://localhost/{user}/axiom.php?module={package}"))
        elif state is RetCode.failed:
            Globals.failed.append((file, f"http://localhost/{user}/axiom.php?module={package}"))            
        else:
            continue
        
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


def run_with_module(*modules, debug=True):

    def generator():
        for package in modules:
            package = package.replace('/', '.').replace('\\', '.')
            module = import_module(package)
            
            if isinstance(module, int):
                state = interpret_int_from_import(module)                    
                file = project_directory() + '/' + package.replace('.', '/') + '.py'
                lapse = None
                latex = None         
            else: 
                try:
                    state, lapse, latex = prove_with_timing(module, debug=debug, slow=True)
                    file = module.__file__
                except AttributeError as e:
                    if re.match("module '[\w.]+' has no attribute 'prove'", str(e)) or re.match("'function' object has no attribute 'prove'", str(e)):
                        from util.search import module_to_py
                        file = module_to_py(package)
                        __init__ = os.path.dirname(file) + '/__init__.py'
                        basename = os.path.basename(file)[:-3]
                        for line in Text(__init__):
                            if re.match('from \. import %s' % basename, line):
                                for line in run(package, debug=False):
                                    m = re.match(r"seconds costed = (\d+\.\d+)", line)
                                    if m:
                                        lapse = float(m[1])
                                        continue
                                        
                                    m = re.match(r"exit_code = (\S+)", line)
                                    if m:
                                        state = int(m[1])
                                        if state > 0:
                                            state = RetCode.proved
                                        elif state < 0:
                                            state = RetCode.failed
                                        else:
                                            state = RetCode.plausible                                            
                                        continue
                                    
                                    m = re.match(r"latex results are saved into: (\S+)", line)
                                    if m:
                                        sql = m[1]
                                        text = Text(sql)
                                        for line in text:
                                            m = re.match('update tbl_axiom_py set state = "\w+", lapse = \S+, latex = ("[\s\S]+") where user = "\w+" and axiom = "\S+"', line)
                                            if m:
                                                latex = eval(m[1])

                                        text.close()
                                        os.unlink(sql)
                                        continue
                                    
                                    print(line.rstrip())
                                break
                    else: 
                        continue
                
            yield package, file, state, lapse, latex                        

    for args in post_process(generator()):
        print('\v'.join((str(arg) for arg in args)).encode(encoding='utf8'))
    
    print_summary()
    
    if Globals.plausible: 
        exit_code = 0
    elif Globals.failed:
        exit_code = -1
    else:
        exit_code = 1
        
    print('exit_code =', exit_code)
    exit(exit_code)


if __name__ == '__main__':
    is_http = 'HTTP_HOST' in os.environ
    if is_http:
        print("Content-type:text/html\n")        
        QUERY_STRING = os.environ['QUERY_STRING']
#         print("QUERY_STRING =", QUERY_STRING, "<br>")
        
        if not QUERY_STRING:
            kwargs = {}            
        else:
            kwargs = {key: value for key, value in map(lambda s: s.split('='), QUERY_STRING.split('&'))}
        
#         print("kwargs =", kwargs, "<br>")        
        args = ''
        
    else: 
        args, kwargs = args_kwargs(sys.argv[1:])
        
    if kwargs:
        if 'clean' in kwargs:
            clean()

    debug = kwargs.pop('debug', False)
    parallel = kwargs.pop('parallel', True)    
    if not args:
        if kwargs:
            for key, value in kwargs.items():
                if key == 'module':
                    run_with_module(value, debug=debug)                    
                elif key == 'hierarchy':
                    from util.hierarchy import insert_into_hierarchy
                    insert_into_hierarchy()
        else:
            if is_http:
                print('''
<style type="text/css">
body {
    background-color: rgb(199, 237, 204);
    margin-left: 1.5em;
}
</style>

<script>
var ret = setInterval(()=>{
    var textarea = document.querySelector('textarea');
    if (textarea){
        console.log("textarea.scrollTop = textarea.scrollHeight;");
        textarea.scrollTop = textarea.scrollHeight;
    }
},
1000);
</script>

<textarea
readonly=true 
spellcheck=false
style="height:100%; width:100%; overflow:auto; word-break:break-all; background-color:rgb(199, 237, 204);">
''')
                prove(debug=debug, parallel=parallel)
                print(r'''</textarea>
<div></div>
<script>
var textarea = document.querySelector('textarea');
var lines = textarea.value;
lines = lines.split(/\n/);
var div = document.querySelector('div');
for (let line of lines){
    if (line.endsWith('.py'))
        continue;
        
    var el;
    if (line.startsWith('http')){
        el = document.createElement('a');
        el.href = line;
        line = line.match(/module=(\S+)/)[1];
        el.innerText = line;
    }
    else{
        el = document.createElement('p');
        el.innerText = line;
    }
    
    div.appendChild(el);
}
textarea.remove();
el.scrollIntoView();
clearInterval(ret);
</script>''')
            else:
                prove(debug=debug, parallel=parallel)
            
    else: 
        run_with_module(*args)
