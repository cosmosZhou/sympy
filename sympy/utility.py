
from sympy.core.relational import Equality, Relational
import sympy
import os
from sympy.logic.boolalg import equivalent_ancestor, Boolean
import traceback
from sympy.logic import boolalg
from sympy.utilities.iterables import topological_sort_depth_first
from builtins import isinstance


def init(func):

    def _func(*args, **kwrags):
        Eq.clear()
        func(*args, **kwrags)

    return _func


sympy.init_printing()
# https://www.programiz.com/python-programming/operator-overloading


class Eq:

    def __init__(self, txt):
        self.__dict__['list'] = []
        
        from sympy.utilities.misc import Text

        self.__dict__['file'] = Text(txt)
        self.file.clear()

    def __del__(self):
#         print('calling destructor')
        self.file.home()
        lines = []        
#         print('writing .php :', self.file.file.name)
        php = self.file.file.name
#         sep = os.sep
        php = php.replace('\\', '/')        
#         utility_php = re.compile(r'\\\w+').sub(r'\\utility', re.compile(r'\w+\\').sub(r'..\\', php[php.index('axiom'):]))        
        utility_php = re.compile(r'/\w+').sub('/utility', re.compile(r'\w+/').sub('../', php[php.index('axiom'):]))
        
        php_code = """\
<?php
require_once '%s';
""" % utility_php
        lines.append(php_code)
        
        for line in self.file:            
            i = 0  
            res = []   
            for m in re.finditer(r"\\tag\*{(Eq(?:\[(\d+)\]|\.(\w+)))}", line):
                expr, index, attr = m.group(1), m.group(2), m.group(3)
    
                if i < m.start():
                    res.append(line[i:m.start()])
                    
                assert line[m.start():m.end()] == m.group(0)
                assert line[m.start(1):m.end(1)] == m.group(1)
                
                if index:
                    assert line[m.start(2):m.end(2)] == m.group(2)
                if attr:
                    assert line[m.start(3):m.end(3)] == m.group(3)
    
                if index:
                    index = int(index)
                    eq = self[index]                
                else:  
                    index = attr
                    eq = getattr(self, attr)                             
                
                res.append(line[m.start():m.start(1)])
                    
                if eq.plausible:                    
                    _expr = Eq.reference(self.get_index(Eq.get_equivalent(eq)))
                    print("%s=>%s : %s" % (_expr, expr, eq))
                    res.append(_expr)                
                    res.append('=>')
                elif eq.plausible == False:
                    res.append('~')
                                    
                res.append(expr)                
                res.append(line[m.end(1):m.end()])
                i = m.end()
                
            res.append(line[i:])
            
            lines.append('$text[] = "%s";' % ''.join(res).replace('\\', '\\\\'))
        
        php_code = """\
render(__FILE__, $text);
?>        
"""
        lines.append(php_code)
        
        self.file.write(lines)

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
        elif eq.substituent is not None:
            return eq.substituent
        
    def get_index(self, equivalent):
        if equivalent is None:
            return -1
        if isinstance(equivalent, (list, tuple)):
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
        plausibles = {i : eq for i, eq in enumerate(self) if eq.plausible}

        for k, v in self.__dict__.items():
            if k in ('list', 'file'):
                continue
            if v.plausible:
                plausibles[k] = v
        return plausibles

    def index(self, eq, dummy_eq=True):
        for i, _eq in enumerate(self.list):
            if _eq == eq or (dummy_eq and eq.dummy_eq(_eq)):
                return i
        for k, v in self.__dict__.items():
            if k in ('list', 'file'):
                continue
            if eq == v or (dummy_eq and eq.dummy_eq(v)):
                return k
        return -1

    def append(self, eq):
        self.list.append(eq)
        return len(self.list) - 1

    def __getitem__(self, index):
        if isinstance(index, int):
            return self.list[index]
        return self.__dict__[index]

    def process(self, rhs, index=None, end_of_line='\n'):
        if isinstance(rhs, identity):
            rhs = rhs.equation
        try:
            latex = rhs.latex
        except:
            traceback.print_exc()
            latex = ''

        infix = str(rhs)
        if isinstance(rhs, Boolean):
            index = self.add_to_list(rhs, index)
            if index != -1:
                
                if isinstance(index, int):
                    index = 'Eq[%d]' % index
                else:
                    index = 'Eq.%s' % index

                tag = r'\tag*{%s}' % index

                latex += tag
                infix = '%s : %s' % (index, infix)            
#         self.file.append(r'\[%s\]' % latex)
        self.file.append(r'\(%s\)' % latex, end_of_line)

        print(infix)
        return self

    def __setattr__(self, index, rhs):
        if index in self.__dict__:
            eq = self.__dict__[index]
            if eq.plausible:
                equivalent = rhs.equivalent
                if isinstance(equivalent, list):
                    equivalent = [e for e in equivalent if e.plausible]
                    assert len(equivalent) == 1
                    equivalent, *_ = equivalent                        
                
                while equivalent != eq:
                    if isinstance(equivalent.equivalent, list):
                        equivalent = [e for e in equivalent.equivalent if e.plausible]                         
                        if len(equivalent) == 1:
                            equivalent, *_ = equivalent
                        else:
                            assert eq in equivalent
                            break                            
                    else:
                        equivalent = equivalent.equivalent

#                     if equivalent == eq:
#                         break

        self.process(rhs, index)

    def add_to_list(self, rhs, index=None):
        old_index = self.index(rhs)
        if old_index == -1:
            if rhs.is_BooleanAtom:
                boolalg.process_options(rhs._assumptions, value=bool(rhs))
                return -1
            if index is not None:
                self.__dict__[index] = rhs
                return index
            return self.append(rhs)
        else:
            eq = self[old_index]
            plausible = rhs.plausible
            if plausible is False:
                eq.plausible = False
            elif plausible is None:
                if eq.plausible:
                    eq.plausible = True
            else:
                if eq.plausible is None:
                    rhs.plausible = True
                else:
                    if isinstance(rhs.equivalent, (list, tuple)):
                        if any(id(eq) == id(_eq) for _eq in rhs.equivalent):
                            return old_index
                    if isinstance(rhs.given, (list, tuple)):
                        if any(id(eq) == id(_eq) for _eq in rhs.given):
                            return old_index 
                        
                    if id(rhs.equivalent) != id(eq) and id(rhs) != id(eq):
                        rhs_equivalent = equivalent_ancestor(rhs)
                        if len(rhs_equivalent) == 1:
                            rhs_equivalent, *_ = rhs_equivalent
                            if eq != rhs_equivalent:
                                rhs_equivalent.equivalent = eq
                                hypothesis = rhs_equivalent.hypothesis
                                if hypothesis:
                                    for h in hypothesis:
                                        h.derivative = None
                                else:
                                    rhs_equivalent.equivalent = None
            if isinstance(old_index, int):
                self.list[old_index] = rhs
            else:
                self.__dict__[old_index] = rhs
            return old_index

    def __lshift__(self, rhs):

        if isinstance(rhs, (list, tuple)):
            for arg in rhs:
                self.process(arg, end_of_line='')
            self.file.append('')
        else:
            self.process(rhs)


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
    in_degrees = {u : 0 for u in graph}

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


class identity(boolalg.Invoker):

    @property
    def equation(self):
        return Relational.__new__(Equality, self.expr, self.obj)

    def __call__(self, *args, **kwargs):
        if self.obj.__name__ == 'subs':
            from sympy.concrete.summations import Sum
            from sympy.integrals.integrals import Integral
            if isinstance(self.obj.__self__, Sum) or isinstance(self.obj.__self__, Integral):
                if len(args) == 2:
                    (x, *_), *_ = self.obj.__self__.limits
                    # domain might be different!
                    assert args[0].name == x.name
            else:
                assert len(args) == 1 and isinstance(args[0], Equality)

        obj = self.obj(*args, **kwargs)

        for i in range(-1, -len(self.func) - 1, -1):
            self._args[i][self.index[i]] = obj
            obj = self.func[i](*self._args[i])
            obj = obj.simplify()
        self.obj = obj
        return self

    def __getattr__(self, method):
        if method == "T":
            assert len(self.obj.shape) < 2
        obj = getattr(self.obj, method)
        if not callable(obj):
            if isinstance(obj, tuple):
                self.append()
            elif obj in self.obj.args:
                self.append()
                self.index.append(self.obj.args.index(obj))
            else:
                ...

        self.obj = obj
        return self


def wolfram_decorator(py, func, **kwargs):
    txt = py.replace('.py', '.php')

    eqs = Eq(txt) 
    print("http://localhost/sympy/axiom" + func.__code__.co_filename[len(os.path.dirname(__file__)):-3] + ".php")
    try: 
        if 'wolfram' in kwargs:
            wolfram = kwargs['wolfram']
            if wolfram is not None:
                with wolfram:
                    func(eqs, wolfram)
            else:
                func(eqs, wolfram)
        else:
            func(eqs)
    except Exception as e:
        print(e)
        traceback.print_exc()
        return None

    plausibles = eqs.plausibles_dict
    if plausibles:
        return False

    return True


def check(func=None, wolfram=None):
    if func is not None:
        return lambda py: wolfram_decorator(py, func)
        
    elif wolfram:
        def decorator(func):
            try:
                from wolframclient.evaluation.kernel.localsession import WolframLanguageSession
                wolfram = WolframLanguageSession()
            except:
                wolfram = None
            
            return lambda py: wolfram_decorator(py, func, wolfram=wolfram)

        return decorator


def plausible(apply=None):
    if apply is None:
        s = traceback.extract_stack()
        if s[-2][0] != s[-3][0]:
            return None        
        return True

    def add_to_set(given, given_set, given_list):

        def add_to_set(given, given_set, given_list):
            if given not in given_set:
                given_list.append(given)
                given_set.add(given)
                     
        if given is not None:
            if isinstance(given, (tuple, list)):
                for g in given:
                    add_to_set(g, given_set, given_list)
            else:
                add_to_set(given, given_set, given_list)
        
    def add(statement):
        given_set = set()
        given_list = []
        if isinstance(statement, tuple):            
            
            for s in statement:
                add_to_set(s.given, given_set, given_list)
                assert s.equivalent is None
                                
            if given_list:
                return tuple(given_list) + statement
            return statement
        
        add_to_set(statement.given, given_set, given_list)
        assert statement.equivalent is None
        
        if given_list:
            return tuple(given_list) + (statement,)
        return statement

    def process(s, dependency):
        s.definition_set(dependency)
                
        assert 'plausible' not in s._assumptions
        s._assumptions['plausible'] = True
        
        if s.given is not None:
            if isinstance(s.given, (tuple, list)):
                for g in s.given:
                    g.definition_set(dependency)
            else:
                s.given.definition_set(dependency)

    def plausible(*args, **kwargs):
        statement = apply(*args, **kwargs)
        s = traceback.extract_stack()
        if apply.__code__.co_filename != s[-2][0]:
            if not kwargs.get('evaluate', True):
                return statement
            if isinstance(statement, tuple):
                return [*(s.simplify() for s in statement)]
            return statement.simplify()
        
        dependency = {}
        if isinstance(statement, tuple):
            for s in statement:
                process(s, dependency)
        else:
            process(statement, dependency)
        G = topological_sort_depth_first(dependency)
        if G:
            definition = [s.equality_defined() for s in G]
            
            statement = add(statement)
            if isinstance(statement, tuple):
                return definition + [*statement]
            return definition + [statement]
            
        else:
            return add(statement)

    return plausible


import inspect
import re
from itertools import dropwhile


# https://cloud.tencent.com/developer/ask/222013
def get_function_body(func):
    print()
    print("{func.__name__}'s body:".format(func=func))
    source_lines = inspect.getsourcelines(func)[0]
    source_lines = dropwhile(lambda x: x.startswith('@'), source_lines)
    source = ''.join(source_lines)
    pattern = re.compile(r'(async\s+)?def\s+\w+\s*\(.*?\)\s*:\s*(.*)', flags=re.S)
    lines = pattern.search(source).group(2).splitlines()
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
if __name__ == '__main__':
    ...
