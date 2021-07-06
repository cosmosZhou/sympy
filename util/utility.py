import sympy, os
from sympy.logic.boolalg import Boolean
import traceback
from sympy.utilities.iterables import topological_sort_depth_first
from enum import unique, Enum
from sympy.core.inference import Inference, process_options, equivalent_ancestor
from _collections import deque, defaultdict
from util.search import py_to_module
from os.path import dirname, basename
from util.std import json_encode


def init(func):

    def _func(*args, **kwrags):
        Eq.clear()
        func(*args, **kwrags)

    return _func


sympy.init_printing()
# https://www.programiz.com/python-programming/operator-overloading


class Eq:
    slots = {'list', 'latex', 'debug'}    

    def __init__(self, debug=True): 
        self.__dict__['list'] = []        
        self.__dict__['latex'] = []
        self.__dict__['debug'] = debug        

    def postprocess(self):
        lines = []
        
        for line in self.latex:
            i = 0  
            res = []   
            for m in re.finditer(r"\\tag\*{(Eq(?:\[(\d+)\]|\.(\w+)))}", line):
                expr, index, attr = m[1], m[2], m[3]
    
                if i < m.start():
                    res.append(line[i:m.start()])
                    
                assert line[m.start():m.end()] == m[0]
                assert line[m.start(1):m.end(1)] == m[1]
                
                if index:
                    assert line[m.start(2):m.end(2)] == m[2]
                if attr:
                    assert line[m.start(3):m.end(3)] == m[3]
    
                if index:
                    index = int(index)
                    eq = self[index]                
                else: 
                    index = attr
                    eq = getattr(self, attr)                             
                
                res.append(line[m.start():m.start(1)])
                    
                if not eq.is_Inference:
                    ...
                elif eq.plausible: 
                    index = self.get_index(Eq.get_equivalent(eq))
                    _expr = Eq.reference(index)
                    
                    if eq.equivalent is not None:
                        if isinstance(eq.equivalent, tuple):
                            arrow = '\N{LEFT RIGHT DOUBLE ARROW}'
                        else:
                            _expr_reference = self[index]
                            if _expr_reference == eq.equivalent:
                                arrow = '\N{LEFT RIGHT DOUBLE ARROW}'
                            elif _expr_reference.equivalent == eq:
                                arrow = '\N{LEFT RIGHT DOUBLE ARROW}'
                            elif _expr_reference == eq.equivalent.given:
                                arrow = '\N{RIGHTWARDS DOUBLE ARROW}'
                            elif _expr_reference == eq.equivalent.imply:
                                arrow = '\N{RIGHTWARDS DOUBLE ARROW}'
                            elif _expr_reference == eq.equivalent.negation:
                                arrow = '='
                            elif _expr_reference == eq.equivalent.equivalent:
                                arrow = '\N{LEFT RIGHT DOUBLE ARROW}'
                            elif index == -1:
                                arrow = '='
                            else:
                                print('index =', index)
                                print('unknown relationship:', _expr, expr)                                
#                                 print('_expr_reference = ')
#                                 print(_expr_reference)
#                                 print(_expr_reference.equivalent)
                                
#                                 print('\neq = ')
#                                 print(eq)
#                                 print(eq.equivalent)
#                                 print(eq.equivalent.negation)
                                arrow = '\N{LEFT RIGHT DOUBLE ARROW}'
                        
                    elif eq.given is not None:
                        arrow = '\N{RIGHTWARDS DOUBLE ARROW}'
                        
                    elif eq.imply is not None:
                        if isinstance(eq.imply.given, (tuple, list)):
                            arrow = '\N{LEFTWARDS ARROW}'
                        else:
                            arrow = '\N{LEFTWARDS DOUBLE ARROW}'
                                
                    else:
                        arrow = '='
                        assert _expr == '?'
                        
                    if self.debug: 
                        print("%s%s%s : %s" % (_expr, arrow, expr, eq))                        

                    res.append(_expr)                
                    res.append(arrow)
                elif eq.plausible == False:
                    res.append('~')
                                    
                res.append(expr)                
                res.append(line[m.end(1):m.end()])
                i = m.end()
                
            res.append(line[i:])
            lines.append(''.join(res))
        
        return '\n'.join(lines)

    @staticmethod   
    def reference(index):
        if isinstance(index, list):
            return ', '.join(Eq.reference(d) for d in index)
        elif isinstance(index, int):
            if index < 0:
                return "?"
            else:
                return "Eq[%d]" % index
        else:
            return "Eq.%s" % index

    @staticmethod        
    def get_equivalent(eq):
        if eq.equivalent is not None:
            return eq.equivalent
        elif eq.given is not None:
            return eq.given
        elif eq.imply is not None:
            return eq.imply
        
    def get_index(self, equivalent):
        if equivalent is None:
            return -1
        if isinstance(equivalent, (list, tuple, set)):
            _index = []
            for eq in equivalent:
                if eq.plausible:
                    _index.append(self.get_index(eq))

            if len(_index) == 1:
                _index = _index[0]
            if not _index:
                return -1
        else:
            _index = self.index(equivalent, False)
            if _index == -1:
                equivalent = Eq.get_equivalent(equivalent)
                return self.get_index(equivalent)
        return _index
        
    @property
    def plausibles_dict(self):
        plausibles = {i: eq for i, eq in enumerate(self) if eq.plausible}

        for k in self.__dict__.keys() - self.slots:
            v = self.__dict__[k]
            if v.plausible:
                plausibles[k] = v
        return plausibles

    def index(self, eq, dummy_eq=True):
        for k in self.__dict__.keys() - self.slots:
            v = self.__dict__[k]
            if eq == v or (dummy_eq and eq.dummy_eq(v)):
                return k
        for i, _eq in enumerate(self.list):
            if _eq.is_Inference:
                _eq = _eq.cond
                
            if eq.is_Inference:
                eq = eq.cond
            
            if _eq == eq or (dummy_eq and eq.dummy_eq(_eq)):
                return i
        return -1

    def append(self, eq):
        self.list.append(eq)
        return len(self.list) - 1

    def __getitem__(self, index):
        if isinstance(index, int):
            return self.list[index]
        return self.__dict__[index]

    def process(self, rhs, index=None, flush=True): 
        latex = rhs.latex
    
        infix = str(rhs)
            
        if isinstance(rhs, Inference):
            index = self.add_to_list(rhs, index)
            if index != -1:
                if isinstance(index, int):
                    index = 'Eq[%d]' % index
                else:
                    index = 'Eq.%s' % index

                tag = r'\tag*{%s}' % index
                    
                latex += tag
                infix = '%s : %s' % (index, infix)
            
        if self.debug:
            print(infix)
                        
        latex = r'\[%s\]' % latex
        #             latex = r'\(%s\)' % latex
#         http://www.public.asu.edu/~rjansen/latexdoc/ltx-421.html
        
        if flush:
            self.latex.append(latex)
        else:
            return latex 

    def __setattr__(self, index, rhs):
        if index in self.__dict__:
            eq = self.__dict__[index]
            if eq.plausible:
                assert rhs.is_equivalent_of(eq) or rhs.is_given_by(eq)

        self.process(rhs, index)

    def add_to_list(self, rhs, index=None):
        old_index = self.index(rhs)
        if old_index == -1:
            if rhs.is_BooleanAtom:
                process_options(value=bool(rhs), **rhs._assumptions)
                return -1
            if index is not None:
                self.__dict__[index] = rhs
                return index
            return self.append(rhs)
        else:
            lhs = self[old_index]
            plausible = rhs.plausible
            if plausible is False:
                lhs.plausible = False
            elif plausible is None:
                if lhs.plausible:
                    lhs.plausible = True
            else:
                if lhs.plausible is None:
                    given = rhs.given
                    equivalent = rhs.equivalent
                    rhs.plausible = True
                    
                    if given is None:
                        if equivalent is not None:
                            if not isinstance(equivalent, (list, tuple)):
                                equivalent.equivalent = lhs
                                                    
                elif lhs.plausible is False:
                    rhs.plausible = False
                else:
                    if isinstance(rhs.equivalent, (list, tuple)):
                        if any(lhs is _eq for _eq in rhs.equivalent):
                            return old_index
                        
                    if rhs.given is not None:
                        if isinstance(rhs.given, (list, tuple)):
                            if any(lhs is _eq for _eq in rhs.given):
                                return old_index
                    
                    if rhs.equivalent is not lhs and rhs is not lhs:
                        lhs_is_plausible = 'plausible' in lhs._assumptions
                        
                        rhs_equivalent = equivalent_ancestor(rhs)
                        if len(rhs_equivalent) == 1:
                            [rhs_equivalent] = rhs_equivalent
                                        
                            if lhs != rhs_equivalent or rhs.given is not None:
                                rhs_plausibles, rhs_is_equivalent = rhs_equivalent.plausibles_set()
                                if len(rhs_plausibles) == 1:
                                    [rhs_plausible] = rhs_plausibles
                                    if rhs_plausible is not lhs:
                                        if rhs_is_equivalent:
                                            lhs_plausibles, lhs_is_equivalent = lhs.plausibles_set()
                                            if len(lhs_plausibles) == 1:
                                                [lhs_plausible] = lhs_plausibles
                                                if lhs_is_equivalent:
                                                    lhs_plausible.equivalent = rhs_plausible
                                                else:
                                                    rhs_plausible.given = lhs_plausible
                                            else:
                                                rhs_plausible.equivalent = lhs
                                        else: 
                                            lhs_plausibles, lhs_is_equivalent = lhs.plausibles_set()
                                            if lhs_is_equivalent:
                                                assert rhs_plausible not in lhs_plausibles, 'cyclic proof detected'
                                                
                                                lhs_plausibles = [*lhs_plausibles]
                                                if len(lhs_plausibles) == 1:
                                                    [lhs_plausible] = lhs_plausibles
                                                    lhs_plausible.given = rhs_plausible
                                                else: 
                                                    rhs_plausible.imply = lhs_plausibles
                                            else:
                                                lhs_plausibles, lhs_is_equivalent = lhs.plausibles_set(clue='imply')
                                                assert not lhs_is_equivalent                                                
                                                if len(lhs_plausibles) == 1: 
                                                    operations = []
                                                    
                                                    cond = lhs
                                                    
                                                    clue = cond.clue
                                                    while clue:
                                                        if clue == 'equivalent':
                                                            imply = cond.equivalent                                                                                                                     
                                                        else:
                                                            assert clue == 'imply'
                                                            imply = cond.imply
                                                            clue = 'given'

                                                        operations.append((imply, clue))
                                                        cond = imply
                                                                                                                    
                                                        clue = cond.clue
                                                    
                                                    operations.reverse()
                                                    
                                                    target = rhs
                                                    while operations:
                                                        imply, clue = operations.pop()
                                                        if imply.clue is not None: 
                                                            setattr(imply, imply.clue, None)
                                                        setattr(imply, clue, target)
                                                        target = imply
                                                        
                                else:
                                    plausibles_set, is_equivalent = lhs.plausibles_set()
                                    if len(plausibles_set) == 1:
                                        [lhs_plausible] = plausibles_set
                                        if is_equivalent: 
                                            if rhs_is_equivalent:
                                                rhs_plausibles.discard(lhs_plausible)
                                                lhs_plausible.equivalent = [*rhs_plausibles]
                                            else: 
                                                assert lhs_plausible not in rhs_plausibles, 'cyclic proof detected'
                                                lhs_plausible.given = [*rhs_plausibles]
                                        else: 
                                            lhs_plausible.imply = rhs_equivalent
                        else:
                            rhs_plausibles, rhs_is_equivalent = rhs.plausibles_set()
                            if len(rhs_plausibles) == 1:
                                [rhs_plausible] = rhs_plausibles
                                if not lhs_is_plausible:
                                    lhs_equivalent = equivalent_ancestor(lhs)
                                    if len(lhs_equivalent) == 1:
                                        [lhs_equivalent] = lhs_equivalent
                                        lhs_equivalent.given = rhs_plausible
                            else: 
                                lhs_plausibles, lhs_is_equivalent = lhs.plausibles_set()
                                if len(lhs_plausibles) == 1:
                                    [lhs_plausible] = lhs_plausibles
                                    if rhs_is_equivalent and lhs_is_equivalent:
                                        ...
                                    else:
                                        if lhs_plausible not in rhs_plausibles: 
                                            lhs_plausible.given = [*rhs_plausibles]
                        if lhs_is_plausible:
                            if 'imply' not in rhs._assumptions: 
                                rhs = lhs                
                                                               
            if isinstance(old_index, int):
                self.list[old_index] = rhs
            else:
                self.__dict__[old_index] = rhs
            return old_index

    def return_index(self, index, rhs):
        if isinstance(index, int):
            self.list[index] = rhs
        else:
            self.__dict__[index] = rhs
        return index
        
    def __lshift__(self, rhs):
        if isinstance(rhs, (list, tuple)): 

            def yield_from(container):
                for e in container:
                    if isinstance(e, (list, tuple)):
                        yield from yield_from(e)
                    else:
                        yield self.process(e, flush=False)

            self.latex.append(''.join(yield_from(rhs)))
        else:
            self.process(rhs)
        return self

    def __ilshift__(self, rhs):
        return self << rhs


def show_latex():
    import matplotlib.pyplot as plt
    ax = plt.subplot(111)
#     defaultFamily
    ax.text(0.1, 0.8, r"$\int_a^b f(x)\mathrm{d}x$", fontsize=30, color="red")
    ax.text(0.1, 0.3, r"$\sum_{n=1}^\infty\frac{-e^{i\pi}}{2^n}!$", fontsize=30)
    plt.show()
# https://www.cnblogs.com/chaosimple/p/4031421.html


def test_latex_parser():
    from sympy.parsing.latex import parse_latex
    expr = parse_latex(r"\frac {1 + \sqrt {\a}} {\b}")  # doctest: +SKIP
    print(expr)


def topological_sort(graph):
    in_degrees = {u: 0 for u in graph}

    vertex_num = len(in_degrees)
    for u in graph:
        for v in graph[u]:
            in_degrees[v] += 1
    Q = [u for u in in_degrees if in_degrees[u] == 0]
    Seq = []
    while Q:
        u = Q.pop()
        Seq.append(u)
        for v in graph[u]:
            in_degrees[v] -= 1
            if in_degrees[v] == 0:
                Q.append(v)

    if len(Seq) == vertex_num:
        return Seq

#         print("there's a circle.")
    return None


def wolfram_decorator(py, func, debug=True, **kwargs):
    eqs = Eq(py.replace('.py', '.php'), debug=debug)
    website = "http://localhost" + func.__code__.co_filename[len(dirname(dirname(dirname(__file__)))):-3] + ".php"
    try: 
        wolfram = kwargs['wolfram']
        with wolfram: 
            func(eqs, wolfram)
    except Exception as e:
        print(e)
        traceback.print_exc()
        print(website)
        return
    
    if debug:
        print(website)
    plausibles = eqs.plausibles_dict
    if plausibles:
        return False

    return True


@unique
class RetCode(Enum):
    proved = ()  # 0
    failed = ()  # 1
    plausible = ()  # 2    
    unproved = ()  # 3 
    unprovable = ()  # 4
    slow = ()  # 5

    def __str__(self):
        return self.name
    
    def __new__(cls):
        value = len(cls.__members__)
        obj = object.__new__(cls)
        obj._value_ = value
        return obj


def run():
    s = traceback.extract_stack()
    if len(s) == 2:
        file = s[0].filename
    else:
        file = s[5].filename
        
    package = py_to_module(file)
    
    from run import prove_with_timing, import_module
    
    res = import_module(package, debug=False)
    from util import MySQL
    try:
        state, lapse, latex = prove_with_timing(res, debug=True, slow=True)        
        
        sql = "replace into tbl_axiom_py values('%s', '%s', '%s', %s, %s)" % (user, package, state, lapse, json_encode(latex))
    #     print(sql)
    except AttributeError as e: 
        if re.match("module '[\w.]+' has no attribute 'prove'", str(e)) or re.match("'function' object has no attribute 'prove'", str(e)): 
            __init__ = os.path.dirname(file) + '/__init__.py'
            basename = os.path.basename(file)[:-3]
            for i, line in enumerate(Text(__init__)):
                if re.match('from \. import %s' % basename, line):
                    Text(__init__).insert(i, "del " + basename)
                    from run import run
                    run(package)
                    break                    
            return
        else: 
            sql = analyze_results_from_run(res, latex=False)        
    
    MySQL.instance.execute(sql)
    if file.endswith("__init__.py"):
        import sys
        sys.exit()


def analyze_results_from_run(lines, latex=True):
    for line in lines:
        line = line.rstrip()
        m = re.match(r'latex results are saved into: (\S+)', line)
        if m:
            sqlFile = m[1]                        
        print(line)

    file = Text(sqlFile)

    sql, *_ = file
    
    file.file.close()
# PermissionError: [WinError 32] 另一个程序正在使用此文件，进程无法访问。: 'C:\\Users\\dell\\AppData\\Local\\Temp/****.sql'
    os.unlink(sqlFile)
       
    if latex: 
        m = re.match('exit_code = (\S+)', line)
        assert m, line                
        ret = int(m[1])
        if ret < 0:
            ret = RetCode.failed
        elif ret > 0:
            ret = RetCode.proved
        else:
            ret = RetCode.plausible

        m = re.match("replace into tbl_axiom_py values(\(.+\));$", sql)
        assert m, sql
        * _, latex = eval(m[1])
        return ret, latex
    else:
        return sql[:-1]
    

from sympy.utilities.misc import Text


def from_axiom_import(py, section, eqs):
    file = Text(py)
    codes = []
    for line in file:
        codes.append(line)
        if re.match('def prove\(', line):
            break
    
    firstStatement, *restLines = file
    if re.match(' +from +axiom +import +', firstStatement):
        firstStatement += ", " + section
    else: 
        codes.append('    from axiom import ' + section)
    codes.append(firstStatement)
    codes += restLines
    file.writelines(codes)
    
    import run
    lines = run.run(py_to_module(py), debug=False)
    
    try:
        return analyze_results_from_run(lines)
    except Exception as e:
        print(e)
        traceback.print_exc()
        return RetCode.failed, eqs.postprocess()       
    

def _prove(func, debug=True, **_):
    py = func.__code__.co_filename
    
    website = f"http://localhost/{basename(dirname(dirname(__file__)))}/axiom.php/{py_to_module(py, '/')}"
    
    eqs = Eq(debug=debug)
    
    try: 
        func(eqs)
        
        if debug:
            print(website)
            
        ret = RetCode.plausible if eqs.plausibles_dict else RetCode.proved
        
    except AttributeError as e:
        messages = source_error()
        
        m = re.match("^module 'sympy(?:\.\w+)*\.(algebra|sets|calculus|discrete|geometry|keras|stats)(?:\.\w+)*' has no attribute '(\w+)'$", str(e))
        if m: 
            import_axiom = False
            if m[2] == 'func':
                * _, statement = messages
                statement = statement.strip()
                if statement == 'if not isinstance(self, cls.func):':
                    ...
                else:
                    import_axiom = True                                
            else: 
                import_axiom = True
                
            if import_axiom:
                return from_axiom_import(py, m[1], eqs)
            
        m = re.match("^'(\w+)' object has no attribute '(\w+)'$", str(e))
        if m:
            t = m[1]
            if t == 'function':
                * _, statement = messages            
                statement = statement.strip()
                m = re.search('(?:algebra|sets|calculus|discrete|geometry|keras|stats)(?:\.\w+)+', statement)
                if m:
                    section, *_ = m[0].split('.')
                    return from_axiom_import(py, section, eqs)
            
            elif t[0].isupper():
                kwargs = detect_error_in_invoke(py, e, messages) or detect_error_in_apply(py, e, messages) or detect_error_in_prove(py, e, messages)
                print(json_encode(kwargs))
                if kwargs and not kwargs['error']:
                    kwargs['error'] = str(e)    

        if str(e) == "'NoneType' object has no attribute 'definition_set'":
            lines = Text(py).collect()
            
            for i, line in enumerate(lines):
                if re.match('^def prove\(', line):
                    break
                
                if re.match(r' +return( *| +None *)$', line):
                    __line__ = i
                    code = lines[i - 1] + '\n' + line
            
            __line__ -= skips_in_apply(py)
            
            kwargs = {}
            kwargs['apply'] = True
            kwargs['line'] = __line__
            kwargs['code'] = code
            kwargs.update(get_error_info(e))        
        else:
            kwargs = detect_error_in_prove(py, e, messages) or detect_error_in_apply(py, e, messages) or detect_error_in_sympy(py, e, messages)
                    
        print(json_encode(kwargs))
            
        print(website)
        ret = RetCode.failed
    except Exception as e: 
        messages = source_error()       
        
        kwargs = detect_error_in_prove(py, e, messages) or detect_error_in_apply(py, e, messages) or detect_error_in_imply(py, e, messages) or detect_error_in_axiom(py, e, messages) or detect_error_in_sympy(py, e, messages)
        print(json_encode(kwargs))
        print(website)
        ret = RetCode.failed
    
    return ret, eqs.postprocess()


def skips_in_apply(py):
    skips = 1
    for i, line in enumerate(Text(py)):
        if i:
            if line.strip():
                break
            else:
                skips += 1
    return skips

    
def get_error_info(e):
    return {'error': str(e),
            'type': re.match(r"<class '([.\w]+)'>", str(type(e)))[1]}                

    
def detect_error_in_prove(py, e, messages):
    for i, line in enumerate(messages):
        m = re.fullmatch(r'File "([^"]+\.py)", line (\d+), in prove', line)
        if m:
            __line__ = int(m[2]) - 1
            pyFile = m[1]
            assert py == pyFile
            i += 1
            code = messages[i]
            lines = Text(pyFile).collect()
            for i, line in enumerate(lines):
                if re.match(r"^def prove\(", line):
                    if __line__ > i:
                        i += 1
                        
                        start = i
                        skips = 0
                        if re.match("    from axiom import \w+", lines[i]):
                            i += 1
                            skips += 1
                            
                        while not lines[i].strip():
                            i += 1
                            skips += 1
                        
                        while i < __line__:
                            if not lines[i].strip(): 
                                skips += 1
                            i += 1
                             
                        __line__ -= start + skips
                    break
            
            kwargs = {}
            kwargs['prove'] = True
            kwargs['line'] = __line__
            kwargs['code'] = code
            kwargs.update(get_error_info(e))
            return kwargs            
    

def detect_error_in_apply(py, e, messages, index=-3):
    for i, line in enumerate(messages):
        m = re.fullmatch(r'File "([^"]+\.py)", line (\d+), in apply', line)
        if m:
            __line__ = int(m[2]) - 1
            i += 1
            pyFile = m[1]
            code = messages[i]
            
            __line__ -= skips_in_apply(pyFile)
            
            kwargs = {}
            kwargs['apply'] = True
            kwargs['line'] = __line__
            kwargs['code'] = code
            kwargs.update(get_error_info(e))
            
            if pyFile != py:
                m = re.search(r"\baxiom[/\\](.+)\.py", pyFile)
                if m:
                    kwargs['module'] = m[1]  # .replace(os.path.sep, '.')
                else:
                    messages = source_error(index)
                    return detect_error_in_invoke(py, e, messages, index=index - 1)
            return kwargs


def detect_error_in_imply(py, e, messages, index=-3):
    for line in messages:
        m = re.fullmatch(r'File "([^"]+\.py)", line (\d+), in imply', line)
        if m:
            messages = source_error(index)
            return detect_error_in_prove(py, e, messages) or detect_error_in_apply(py, e, messages, index=index - 1)
        

def detect_error_in_invoke(py, e, messages, index=-3):
    for line in messages:
        m = re.fullmatch(r'File "([^"]+[\\/]invoker\.py)", line (\d+), in (\w+)', line)
        if m:
            if m[3] in ('__getattr__', 'invoke', '__call__'):
                messages = source_error(index)
                return detect_error_in_prove(py, e, messages) or detect_error_in_invoke(py, e, messages, index=index - 1)


def detect_error_in_sympy(py, e, messages, index=-3):
    for line in messages:
        m = re.fullmatch(r'File "([^"]+[\\/]sympy[\\/]([^"]+)\.py)", line (\d+), in (\w+)', line)
        if m:
            messages = source_error(index)
            return detect_error_in_apply(py, e, messages) or detect_error_in_prove(py, e, messages) or detect_error_in_invoke(py, e, messages, index=index - 1) or detect_error_in_sympy(py, e, messages, index=index - 1)


def detect_error_in_axiom(py, e, _messages, index=-3):
    for line in _messages:
        m = re.fullmatch(r'File "([^"]+[\\/]axiom[\\/]([^"]+)\.py)", line (\d+), in (\w+)', line)
        if m:
            messages = source_error(index)
            kwargs = detect_error_in_apply(py, e, messages) or detect_error_in_prove(py, e, messages) or detect_error_in_invoke(py, e, messages, index=index - 1)
            if kwargs:
                if isinstance(e, AssertionError):
                    if not kwargs['error']:
                        kwargs['error'] = _messages[1]
                        
                return kwargs


def unprovable(func):

    def unprovable(**kwargs):
        _, latex = _prove(func, **kwargs)
        return RetCode.unprovable, latex

    return unprovable


def unproved(func):

    def unproved(**kwargs):
        _, latex = _prove(func, **kwargs)
        return RetCode.unproved, latex

    return unproved


def slow(func):

    def slow(**kwargs): 
        if kwargs.pop('slow', False):
            return _prove(func, **kwargs)
        else:
            from util import MySQL
            [[latex]] = MySQL.instance.select(f"select latex from tbl_axiom_py where user = '{user}' and axiom = '{py_to_module(func.__code__.co_filename, '.')}'")            
            return RetCode.slow, latex
    
    return slow

    
funcptr = {
    ('proved', False): unproved,
    ('unproved', True): unproved,
    ('provable', False): unprovable,
    ('unprovable', True): unprovable,
    ('slow', True): slow,
}


def prove(*args, **kwargs):
    if args:
        return lambda **kwargs: _prove(*args, **kwargs)    
        
    for key, value in kwargs.items():
        return funcptr[(key, value)]

    
def wolfram(func):

    def decorator(func):
        from wolframclient.evaluation.cloud import cloudsession
        session = cloudsession.session
# from wolframclient.evaluation.kernel.localsession import WolframLanguageSession
# session = WolframLanguageSession()
        
        return lambda py, **kwargs: wolfram_decorator(py, func, wolfram=session, **kwargs)

    return decorator


def apply(*args, **kwargs):
    if args:
        assert len(args) == 1
        axiom = args[0]
        if axiom.__module__ == '__main__':
            paths = axiom.__code__.co_filename[len(dirname(__file__)):].split(os.sep)
        else:
            paths = axiom.__module__.split('.')
            
        if 'given' in paths:
            return given(axiom, **kwargs)
        else:
            return imply(axiom, **kwargs)
    else:
        return lambda axiom: apply(axiom, **kwargs)


def imply(apply, **kwargs):
    is_given = kwargs['given'] if 'given' in kwargs else True
    simplify = kwargs['simplify'] if 'simplify' in kwargs else True
    
    def add(given, statement):
        if isinstance(statement, tuple):
            if given is None:
                return statement
            
            if isinstance(given, tuple):
                return given + statement
            
            return (given,) + statement
        
        if given is None:
            return statement
        
        if isinstance(given, tuple):
            return given + (statement,)
        
        return (given, statement)

    def process(s, dependency):
        s.definition_set(dependency)
                
        if 'plausible' not in s._assumptions:
            s = Inference(s, plausible=True)
            
        return s

    def imply(*args, **kwargs):
        # nonlocal simplify
        _simplify = kwargs.pop('simplify', True) and simplify

        __kwdefaults__ = apply.__kwdefaults__
        if __kwdefaults__ is not None and 'simplify' in __kwdefaults__ and _simplify != __kwdefaults__['simplify']:
            kwargs['simplify'] = _simplify
            
        statement = apply(*map(lambda inf: inf.cond if isinstance(inf, Inference) else inf, args), **kwargs)        
        
        if is_given:
            given = tuple(eq for eq in args if isinstance(eq, (Boolean, Inference)))
            if len(given) == 1:
                given = given[0]
            elif not given:
                given = None        
        else:
            given = None            
            
        s = traceback.extract_stack()
        if apply.__code__.co_filename != s[-2][0]:
            
            if given is None:
                if isinstance(statement, tuple): 
                    statement = tuple(s.copy(plausible=None, evaluate=False) for s in statement)
                else: 
                    statement = statement.copy(plausible=None, evaluate=False)
                                    
                    if _simplify and len(args) == 1 and \
                    (statement.is_Equal or statement.is_Equivalent) \
                    and args[0] is statement.lhs:
                        _simplify = False                
            else: 
                if isinstance(given, tuple):
                    is_not_False = all(g.plausible is not False for g in given)
                else:
                    is_not_False = given.plausible is not False
                    
                assert is_not_False , 'a False proposition can not be used to imply any other proposition!'
                    
                if isinstance(statement, tuple): 
                    statement = tuple(s.copy(given=given, evaluate=False) for s in statement)
                else: 
                    statement = statement.copy(given=given, evaluate=False)
                    
            if not _simplify:
                if isinstance(statement, (list, tuple)) or statement.is_Inference:
                    return statement
                
                return Inference(statement, plausible=None)
            
            if isinstance(statement, (list, tuple)):
                return tuple(s.simplify(emplace=True) for s in statement)
            
            return statement.simplify(emplace=True)            
        
        dependency = {}
        if isinstance(statement, tuple):
            statement = tuple(process(s, dependency) for s in statement)                
        else:
            statement = process(statement, dependency)
            
        if given is not None:
            if isinstance(given, tuple):
                for g in given:
                    g.definition_set(dependency)

                given = tuple(Inference(g, plausible=None) for g in given) 
            else:
                given.definition_set(dependency)                
                given = Inference(given, plausible=None)

        G = topological_sort_depth_first(dependency)
        if G:
            definition = tuple(s.equality_defined() for s in G)
            
            statement = add(given, statement)
            if isinstance(statement, tuple):
                return definition + statement
            return definition + (statement,)
            
        else:
            return add(given, statement)

    return imply


def given(apply, **kwargs):
    is_given = kwargs['given'] if 'given' in kwargs else True
    simplify = kwargs['simplify'] if 'simplify' in kwargs else True
    
    def add(given, statement):
        if isinstance(statement, tuple):
            if given is None:
                return statement
            
            if isinstance(given, tuple):
                return tuple(given) + statement
            
            return (given,) + statement
        
        if given is None:
            return statement
        
        if isinstance(given, tuple):
            return tuple(given) + (statement,)
        
        return (given, statement)

    def process(s, dependency):
        s.definition_set(dependency)
                
        if 'plausible' in s._assumptions:
            del s._assumptions['plausible']
        s = Inference(s, plausible=None)
        return s

    def given(*args, **kwargs):
#         nonlocal simplify
        _simplify = kwargs.pop('simplify', True) and simplify
        
        statement = apply(*map(lambda inf: inf.cond if isinstance(inf, Inference) else inf, args), **kwargs)
        
        i = 0        
        if isinstance(args[i], Inference):
            imply, *args = args
        else: 
            while isinstance(args[i], Boolean):
                i += 1
                if i == len(args):
                    break

            imply, args = args[:i], args[i:]
            if len(imply) == 1:
                [imply] = imply
        
        s = traceback.extract_stack()
        if apply.__code__.co_filename != s[-2][0]: 
            if isinstance(statement, tuple):
                if isinstance(imply, tuple):
                    statement = tuple(s.copy(imply=imply) for s in statement)
                    if _simplify:
                        statement = tuple((s.simplify(emplace=True) for s in statement))
                        
                    return statement
                elif imply.is_Inference:
                    statement = tuple(s.copy(imply=imply) for s in statement)
                    if _simplify:
                        statement = tuple((s.simplify(emplace=True) for s in statement))
                    
                    imply.given = statement
                    return statement
                
                from sympy import And
                statement = And(*statement, imply=imply)                
            else:
                statement = statement.copy(imply=imply)
                
            if _simplify:
                statement = statement.simplify(emplace=True)
            
            return statement
        
        dependency = {}
        if isinstance(statement, tuple):
            statement = tuple(process(s, dependency) for s in statement)
        else: 
            statement = process(statement, dependency)
        
        if isinstance(imply, tuple):
            for g in imply:
                g.definition_set(dependency)

            imply = tuple(Inference(g, plausible=True) for g in imply) 
        else:
            assert not imply.is_Inference
            imply.definition_set(dependency)
            imply = Inference(imply, plausible=True)
            
        statement = add(imply, statement)
        
        G = topological_sort_depth_first(dependency)
        if G:
            definition = [s.equality_defined() for s in G]
            
            if isinstance(statement, tuple):
                statement = definition + [*statement]
            else:
                statement = definition + [statement]
                
        return statement

    return given


import re


# https://cloud.tencent.com/developer/ask/222013
def get_function_body(func):
    import inspect
    from itertools import dropwhile    
    print("{func.__name__}'s body:".format(func=func))
    source_lines = inspect.getsourcelines(func)[0]
    source_lines = dropwhile(lambda x: x.startswith('@'), source_lines)
    source = ''.join(source_lines)
    pattern = re.compile(r'(async\s+)?def\s+\w+\s*\(.*?\)\s*:\s*(.*)', flags=re.S)
    lines = pattern.search(source)[2].splitlines()
    if len(lines) == 1:
        return lines[0]
    else:
        indentation = len(lines[1]) - len(lines[1].lstrip())
        return '\n'.join([lines[0]] + [line[indentation:] for line in lines[1:]])

# https://en.wikipedia.org/wiki/Topological_sorting#
# http://latex.91maths.com/
# http://ctex.math.org.cn/blackboard.html
# https://tex.stackexchange.com/questions/256644/convert-latex-to-sympy-format
# https://cloud.tencent.com/developer/article/1057779
# http://www.wiris.com/plugins/demo/ckeditor4/php/
# https://docs.wiris.com/en/mathtype/mathtype_web/sdk-api/embedding
# http://www.wiris.com/editor/demo/en/developers
# https://zh.numberempire.com/latexequationeditor.php
# https://www.numberempire.com/latexequationeditor.php
# ..................................................\\

# http://www.sagemath.org/download-source.html
# https://www.sagemath.org/


def assert_hashly_equal(lhs, rhs):
    assert lhs._hashable_content() == rhs._hashable_content(), "hash(%s) != hash(%s), \nsince %s \n!= \n%s" % (lhs, rhs, lhs._hashable_content(), rhs._hashable_content())


def recursive_construct(parentheses, depth):
    mid = len(parentheses) // 2
    start = parentheses[:mid]
    end = parentheses[mid:]

    if start in {"(", ")", "{", "}"}:
        start = "\\" + start
        end = "\\" + end

    if depth == 1:
        return "%s[^%s]*%s" % (start, parentheses, end)
    return "%s[^%s]*(?:" % (start, parentheses) + recursive_construct(parentheses, depth - 1) + "[^%s]*)*%s" % (parentheses, end)


def balancedGroups(parentheses, depth, multiple=True):
    regex = recursive_construct(parentheses, depth)
    if multiple:
        return "((?:%s)*)" % regex
    else:
        return "(?:%s)" % regex


def balancedBrackets(depth, multiple=False):
    return balancedGroups("\[\]", depth, multiple)


def balancedParentheses(depth, multiple=False):
    return balancedGroups("()", depth, multiple)


balancedParanthesis = balancedParentheses(7)


def detect_axiom(statement):
#     // Eq << Eq.x_j_subset.apply(discrete.sets.subset.nonemptyset, Eq.x_j_inequality, evaluate=False)
    matches = re.compile('\.apply\((.+)\)').search(statement)
    if matches:
        theorem = matches[1].split(',')[0].strip()
        
        yield theorem


def detect_axiom_given_theorem(theorem, statement):
    if theorem.startswith('.') or theorem.startswith('Eq'):
#         // consider the case
#         // Eq << Eq[-1].reversed.apply(discrete.sets.ne.notcontains, evaluate=False)

#         // consider the case
#         // Eq[-2].this.args[0].apply(algebra.cond.cond.imply.et, invert=True, swap=True)

        yield from detect_axiom(statement)        
    elif 'Eq.' not in theorem:
        yield theorem
    else:
        yield from detect_axiom(statement)


def dependency_analysis(theorem):
    import axiom    
    prove = eval('axiom.' + theorem).prove
    import inspect
    prove = prove.__closure__[0].cell_contents
    if isinstance(prove, tuple):
        prove = prove[0]
        
    for statement in inspect.getsource(prove).splitlines()[2:]:
#         // remove comments starting with #
        if re.compile('^\s*#.*').match(statement): 
            continue
        
#         // stop analyzing if return statement is encountered.
        statement = statement[4:]
        if re.compile('^return\s*$').match(statement):
            break
        
        if not statement:
            continue
        
#         print(statement, file=sys.stderr)
#    // Eq <<= geometry.plane.trigonometry.sine.principle.add.apply(*Eq[-2].rhs.arg.args), geometry.plane.trigonometry.cosine.principle.add.apply(*Eq[-1].rhs.arg.args)
        matches = re.compile("((?:Eq *<<= *|Eq\.\w+, *Eq\.\w+ *= *)([\w.]+|Eq[-\w.\[\]]*\[-?\d+\][\w.]*)\.apply%s\s*[,&]\s*)(.+)" % balancedParanthesis).match(statement) 
        if matches:
#             // error_log('theorem detected: ' . $theorem);
            first_statement = matches[1]
            yield from detect_axiom_given_theorem(matches[2], first_statement)

            second_statement = matches[3]
            if second_statement != "\\":
                matches = re.compile("([\w.]+|Eq[-\w.\[\]]*\[-?\d+\])\.apply\(").search(second_statement)
                assert matches
                yield from detect_axiom_given_theorem(matches[1], second_statement)
                                    
            continue
        m = re.compile("([\w.]+)\.apply\(").search(statement)
        if m:
#             // error_log('theorem detected: ' . $theorem);
            theorem = m[1]
            yield from detect_axiom_given_theorem(m[1], statement)
            
            continue
        
        matches = re.compile('(=|<<) *apply\(').search(statement)
        if matches:
            continue
#             // error_log('yield statement: ' . $statement);
#             // error_log("php = $php");
# 
#             $yield['module'] = py_to_module(endsWith($python_file, '__init__.py') ? substr($python_file, 0, - strlen('/__init__.py')) . '.php' : $python_file);
        
        yield from detect_axiom(statement)


def filename2module(filename):
    words = filename.replace(os.path.sep, '.').split('.')
    index = words.index('axiom')
    words = words[index + 1:-1]
    if words[-1] == '__init__':
        *words, _ = words
    theorem = '.'.join(words)
    return theorem


def detect_cycle(filename):
    theorem = filename2module(filename)
    G = recursive_parsing(theorem)
    print(G)

        
def recursive_parsing(theorem):
    theoremSet = {*dependency_analysis(theorem)}
    G = defaultdict(list)
    q = deque()
    
    for child in theoremSet:
        q.append(child)
        G[theorem].append(child)
    
    while q:
        theorem = q.popleft()
        
        theoremSetNew = {*dependency_analysis(theorem)}
        theoremSetNew -= theoremSet
        
        if theoremSetNew:
            theoremSet |= theoremSetNew        
            for child in theoremSetNew:
                q.append(child)
                G[theorem].append(child)
            
    return G

        
def chmod():
    if os.sep == '/':  # is Linux system    
        cmd = 'chmod -R 777 axiom'
    #         os.system(cmd)
        for s in os.popen(cmd).readlines():
            print(s)

           
user = os.path.basename(os.path.dirname(os.path.dirname(__file__)))


def source_error(index=-2):
    from traceback import TracebackException
    import sys
    etype, value, tb = sys.exc_info() 
    lines = [*TracebackException(type(value), value, tb, limit=None).format(chain=None)]
    error_source = lines[index]

    print(error_source, file=sys.stderr)
    error_source = error_source.strip()
    return error_source.splitlines()


class cout:

    def __lshift__(self, rhs):
        print(rhs)

        
cout = cout()

if __name__ == '__main__':
    ...
