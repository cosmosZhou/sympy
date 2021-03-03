
import sympy
import os
from sympy.logic.boolalg import equivalent_ancestor, Boolean
import traceback
from sympy.logic import boolalg
from sympy.utilities.iterables import topological_sort_depth_first
import time


def init(func):

    def _func(*args, **kwrags):
        Eq.clear()
        func(*args, **kwrags)

    return _func


sympy.init_printing()
# https://www.programiz.com/python-programming/operator-overloading


class Eq:
    slots = {'list', 'file', 'timing', 'debug'}    

    def __init__(self, php_file, debug=True):
        from sympy.utilities.miscellany import Text
        
        self.__dict__['list'] = []
        self.__dict__['file'] = Text(php_file)
        self.__dict__['timing'] = time.time()
        self.__dict__['debug'] = debug
        
        self.file.clear()
        
        php = self.file.file.name
#         sep = os.sep
        php = php.replace('\\', '/')        

        render_php = re.compile(r'/\w+').sub('/render', re.compile(r'\w+/').sub('../', php[len(os.path.dirname(__file__)) + 1:]))
        php_code = """\
<?php
require_once '%s';
render(__FILE__);        
""" % render_php

        self.file.write(php_code)

    def __del__(self):
#         print('calling destructor')        
        self.file.home()
#         sep = os.sep        
        lines = []
        
        lines.append("<p style='display:none'>timing = %s</p>" % (time.time() - self.timing))
        for line in self.file:
            if not line.startswith('//'):
                lines.append(line)
                continue
                        
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
                    if self.debug:
                        print("%s=>%s : %s" % (_expr, expr, eq))
                    res.append(_expr)                
                    res.append('=>')
                elif eq.plausible == False:
                    res.append('~')
                                    
                res.append(expr)                
                res.append(line[m.end(1):m.end()])
                i = m.end()
                
            res.append(line[i:])
            
#             lines.append('$text[] = "%s";' % ''.join(res).replace('\\', '\\\\'))
            lines.append(''.join(res))
        
        self.file.write(lines)
        self.file.append("?>")        

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
            
        if self.debug:
            print(infix)
                        
        latex = r'\[%s\]' % latex
        #             latex = r'\(%s\)' % latex
#         http://www.public.asu.edu/~rjansen/latexdoc/ltx-421.html
        
        if flush:
            self.file.append('//' + latex)
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
                boolalg.process_options(value=bool(rhs), **rhs._assumptions)
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
                                                    
                    elif not isinstance(given, (list, tuple)):
                        derivative = given.derivative     
                        if isinstance(derivative, (list, tuple)):
                            if all(eq.plausible is None for eq in derivative):
                                given.plausible = True
                                
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
                        else:
                            if rhs.given.plausible is False:
                                eqs = [eq for eq in rhs.given.derivative if lhs.plausible is not None]
                                if len(eqs) == 1:
                                    eqs[0].plausible = False
                    
                    if rhs.equivalent is not lhs and rhs is not lhs:
                        lhs_is_plausible = 'plausible' in lhs._assumptions
                        
                        rhs_equivalent = equivalent_ancestor(rhs)
                        if len(rhs_equivalent) == 1:
                            rhs_equivalent, *_ = rhs_equivalent
                                        
                            if lhs != rhs_equivalent or rhs.given is not None:
                                rhs_plausibles, rhs_is_equivalent = rhs_equivalent.plausibles_set()
                                if len(rhs_plausibles) == 1:
                                    rhs_plausible, *_ = rhs_plausibles
                                    if rhs_plausible is not lhs:
                                        if rhs_is_equivalent:
                                            lhs_plausibles, lhs_is_equivalent = lhs.plausibles_set()
                                            if len(lhs_plausibles) == 1:
                                                lhs_plausible, *_ = lhs_plausibles
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
                                                    lhs_plausible, *_ = lhs_plausibles
                                                    lhs_plausible.given = rhs_plausible
                                                else: 
                                                    rhs_plausible.imply = lhs_plausibles                                            
                                else:
                                    plausibles_set, is_equivalent = lhs.plausibles_set()
                                    if len(plausibles_set) == 1:
                                        lhs_plausible, *_ = plausibles_set
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
                                rhs_plausible, *_ = rhs_plausibles
                            else: 
                                lhs_plausibles, lhs_is_equivalent = lhs.plausibles_set()
                                if len(lhs_plausibles) == 1:
                                    lhs_plausible, *_ = lhs_plausibles
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

            self.file.append('//' + ''.join(yield_from(rhs)))
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
    website = "http://localhost" + func.__code__.co_filename[len(os.path.dirname(os.path.dirname(os.path.dirname(__file__)))):-3] + ".php"
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


def prove(func): 

    def prove(py, func, debug=True):
        eqs = Eq(py.replace('.py', '.php'), debug=debug)
        website = "http://localhost" + func.__code__.co_filename[len(os.path.dirname(os.path.dirname(os.path.dirname(__file__)))):-3] + ".php"
        try: 
            func(eqs)
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

    return lambda py, **kwargs: prove(py, func, **kwargs)


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
            paths = axiom.__code__.co_filename[len(os.path.dirname(__file__)):].split(os.sep)
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
            
            if isinstance(given, list):
                return tuple(given) + statement
            
            return (given,) + statement
        
        if given is None:
            return statement
        
        if isinstance(given, list):
            return tuple(given) + (statement,)
        
        return (given, statement)

    def process(s, dependency):
        s.definition_set(dependency)
                
        if 'plausible' not in s._assumptions:
            s._assumptions['plausible'] = True

    def imply(*args, **kwargs):
        nonlocal simplify
        simplify = kwargs.pop('simplify', True) and simplify
        statement = apply(*args, **kwargs)
        
        if isinstance(statement, tuple):
            for s in statement:
                if s.equivalent is not None:
                    s.equivalent = None
        elif statement.equivalent is not None:
            statement.equivalent = None
            
        if is_given:
            given = [eq for eq in args if isinstance(eq, Boolean)]
            if len(given) == 1:
                given = given[0]
            elif not given:
                given = None        
        else:
            given = None            
            
        s = traceback.extract_stack()
        if apply.__code__.co_filename != s[-2][0]:
            
            if given is not None:
                if isinstance(statement, tuple): 
                    statement = [s.copy(given=given) for s in statement]
                else:
                    statement = statement.copy(given=given)
                
            if not simplify:
                return statement
            if isinstance(statement, list):
                return [*(s.simplify() for s in statement)]
            return statement.simplify()
        
        dependency = {}
        if isinstance(statement, tuple):
            for s in statement:
                process(s, dependency)
        else:
            process(statement, dependency)
            
        if given is not None:
            if isinstance(given, (tuple, list)):
                for g in given:
                    g.definition_set(dependency)
            else:
                given.definition_set(dependency)
            
        G = topological_sort_depth_first(dependency)
        if G:
            definition = [s.equality_defined() for s in G]
            
            statement = add(given, statement)
            if isinstance(statement, tuple):
                return definition + [*statement]
            return definition + [statement]
            
        else:
            return add(given, statement)

    return imply


def given(apply):

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

    def given(*args, **kwargs):
        simplify = kwargs.pop('simplify', True) 
        statement = apply(*args, **kwargs)        
        
        assert not isinstance(statement, tuple)        
        if statement.equivalent is not None:
            statement.equivalent = None
            
        imply, *args = args
        given = tuple(eq for eq in args if isinstance(eq, Boolean))
        
        assert all(g.plausible is None for g in given)
            
        assert imply.is_Boolean
        
        s = traceback.extract_stack()
        if apply.__code__.co_filename != s[-2][0]: 
            statement = statement.copy(imply=imply)
            
            if not simplify:
                return statement
            if isinstance(statement, list):
                return [*(s.simplify() for s in statement)]
            return statement.simplify()
        
        dependency = {}
        process(statement, dependency)
        
        for g in given:
            g.definition_set(dependency)
        
        imply.definition_set(dependency)
        imply._assumptions['plausible'] = True
            
        G = topological_sort_depth_first(dependency)
        if G:
            definition = [s.equality_defined() for s in G]
            
            statement = add((imply,) + given, statement)
            if isinstance(statement, tuple):
                return definition + [*statement]
            return definition + [statement]
            
        else:
            return add((imply,) + given, statement)

    return given


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


def assert_hashly_equal(lhs, rhs):
    assert lhs._hashable_content() == rhs._hashable_content(), "hash(%s) != hash(%s), \nsince %s \n!= \n%s" % (lhs, rhs, lhs._hashable_content(), rhs._hashable_content())


if __name__ == '__main__':
    ...
