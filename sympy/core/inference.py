"""
----
at present Inference is mainly needed for process of theorem proof
"""
from sympy.logic.invoker import Invoker
from sympy.logic.boolalg import And, Suffice, Necessary, Equivalent


class Inference:
    is_Inference = True
    
    def __init__(self, cond, **_assumptions):
        self.cond = cond.cond if cond.is_Inference else cond
        self._assumptions = _assumptions                        

    def __getattr__(self, attr):
        return getattr(self.cond, attr) 

    @property    
    def T(self):
        return Inference(self.cond.T, equivalent=self)        

    @property    
    def equivalent(self):
        return self._assumptions.get('equivalent')
    
    @equivalent.setter
    def equivalent(self, eq):
        if eq is not None:
            assert 'equivalent' not in self._assumptions
            assert not self.is_BooleanFalse and not self.is_BooleanTrue
            assert self is not eq 
            self._assumptions['equivalent'] = eq
            if 'plausible' in self._assumptions:
                del self._assumptions['plausible']
            return

        if 'equivalent' in self._assumptions:
            del self._assumptions['equivalent']
    
    @property    
    def given(self):
        return self._assumptions.get('given')
    
    @given.setter
    def given(self, eq):
        if eq is not None:
            assert self is not eq
            self._assumptions['given'] = eq
            if 'plausible' in self._assumptions:
                del self._assumptions['plausible']
            
            return

        if 'given' in self._assumptions:
            del self._assumptions['given']
    
    @property    
    def imply(self):
        return self._assumptions.get('imply')
    
    @imply.setter
    def imply(self, eq):
        if eq is not None:
            assert self is not eq
            self._assumptions['imply'] = eq
            return

        if 'imply' in self._assumptions:
            del self._assumptions['imply']

# here we define negation = counterproposition    
    @property    
    def negation(self):
        return self._assumptions.get('negation')
    
    @negation.setter
    def negation(self, eq):
        if eq is not None:
            assert 'negation' not in self._assumptions
            self._assumptions['negation'] = eq
            return

        if 'negation' in self._assumptions:
            del self._assumptions['negation']
    
    def plausibles_set(self):
        find_plausibles = self.find_plausibles()        
        result = [*zip(*find_plausibles)]
        if result:
            plausibles_set, is_equivalent = result       
            return {*plausibles_set}, all(is_equivalent)
        return set(), False
        
    def set_equivalence_relationship(self, other):
        plausibles_set, is_equivalent = self.plausibles_set()
        if len(plausibles_set) == 1:
            if is_equivalent:
                eq, *_ = plausibles_set
                if isinstance(other, (list, tuple)):
                    is_equivalent = True
                    plausibles_set = set()
                    for other in other:
                        _plausibles_set, _is_equivalent = other.plausibles_set()
                        plausibles_set |= _plausibles_set
                        is_equivalent &= _is_equivalent
                else:
                    plausibles_set, is_equivalent = other.plausibles_set()
                
                assert eq not in plausibles_set, 'cyclic proof detected'
                    
                equivalent = [*plausibles_set]
                if len(equivalent) == 1:
                    equivalent, *_ = equivalent
                elif not equivalent:
                    return
                
                if is_equivalent:
                    from sympy.core.compatibility import default_sort_key
                    if isinstance(equivalent, (list, tuple)):
                        p, *q = sorted((eq, *equivalent), key=lambda inf: default_sort_key(inf.cond))                    
                    else:
                        p, q = sorted((eq, equivalent), key=lambda inf: default_sort_key(inf.cond))
                    p.equivalent = q
                else:
                    del eq._assumptions['plausible']
                    eq.given = equivalent
                return True
            else:
                eq, *_ = plausibles_set
                if isinstance(other, list):
                    plausibles_set = set()
                    for other in other:
                        _plausibles_set, is_equivalent = other.plausibles_set()
                        plausibles_set |= _plausibles_set
                        if not is_equivalent:
                            return 
                else:
                    plausibles_set, is_equivalent = other.plausibles_set()
                    if not is_equivalent:
                        return 
                
                assert eq not in plausibles_set, 'cyclic proof detected'
                    
                equivalent = [*plausibles_set]
                if len(equivalent) == 1:
                    equivalent, *_ = equivalent
                elif not equivalent:
                    return
                
                del eq._assumptions['plausible']
                eq.given = equivalent
                return True                
        
    def find_plausibles(self, is_equivalent=True):
        if self._assumptions.get('plausible'): 
            yield self, is_equivalent
        else:
            equivalent = self.equivalent        
            if equivalent is None:
                given = self.given
                is_equivalent = False
            else:
                given = equivalent
    
            if given is not None:
                if isinstance(given, (tuple, list, set)): 
                    for given in given:
                        if given.is_Inference:
                            yield from given.find_plausibles(is_equivalent)
                else:
                    if given.is_Inference:
                        yield from given.find_plausibles(is_equivalent)
        
    def induct(self, **kwargs):
        if self.given is not None:
            given = self.given
            if isinstance(given, list):
                given = And(*given)
                
            if kwargs.get('given'):
                return Inference(Necessary(self, given), plausible=None)
            if kwargs.get('deep'):
                inf = given.induct(deep=True, imply=True)
                if inf is not None:
                    return Inference(Suffice(inf.lhs, self), plausible=None)
            return Inference(Suffice(given, self), plausible=None)
        if self.equivalent is not None:
            equivalent = self.equivalent
            if isinstance(equivalent, list):
                equivalent = And(*equivalent)
                
            if kwargs.get('given'):
                return Inference(Necessary(equivalent, self), plausible=None)
            
            if kwargs.get('imply', True):
                if kwargs.get('reverse'):
                    return Inference(Suffice(self, equivalent), plausible=None)
                return Inference(Suffice(equivalent, self), plausible=None)
            
            return Inference(Equivalent(equivalent, self), plausible=None)
        if self.imply is not None:
            imply = self.imply
            if isinstance(imply, list):
                imply = And(*imply)

            if kwargs.get('given'):
                return Inference(Necessary(imply, self), plausible=None)
                
            return Inference(Suffice(self, imply), plausible=None)
    
    def subs_assumptions_for_equality(self, eq, result, simplify=True):
        if eq.plausible:
            if self.plausible: 
                assumptions = {'given': [self, eq]}
            else:
                assumptions = {'given': eq}
        else:
            if self.plausible:
                result &= self.domain_definition()
                
            assumptions = {'equivalent': self}
        self = result.copy(**assumptions)
        if simplify:
            self = self.simplify()
        return self
    
    def __bool__(self):
        return bool(self.cond)

    def __str__(self):
        return str(self.cond)
    
    __repr__ = __str__
    
    @property
    def this(self):
        return Invoker(self)
    
    @property
    def clue(self):
        if self._assumptions:
            clue, *_ = self._assumptions.keys()
            if clue != 'plausible':
                return clue
    
    def apply(self, axiom, *args, split=True, **kwargs):
        if self.is_And:
            if axiom.__name__.split(sep='.', maxsplit=3)[2] == 'et':
                split = False
                
            if split: 
                args = []
                funcs = []
                
                depth = kwargs.pop('depth', None)
                if not depth:
                    args = [*self.args]
                else:
    
                    def instantiate(eq):
                        function = eq
                        for _ in range(depth):
                            function = function.function
                        return function
                    
                    for eq in self.args: 
                        if eq.is_ConditionalBoolean:
                            _funcs, function = eq.funcs()
                            _funcs = _funcs[-depth:]
                            if funcs:
                                assert _funcs == funcs
                            else: 
                                funcs = _funcs
                            function = instantiate(eq)
                            args.append(function)
                        else:
                            args.append(eq)
                            
                function = axiom.apply(*args, **kwargs)
                clue = function.clue
                for func, limits in funcs:
                    function = func(function, *limits)
                
                if function.is_BooleanAtom:
                    return function.copy(**{clue: self})
                
                function.set_clause(clue, self, force=True)
                
                if kwargs.get('simplify', True):
                    function = function.simplify()
                return function
            
        eqs = axiom.apply(self, *args, **kwargs)
        if isinstance(eqs, (list, tuple)):
            eqs = And(*eqs, equivalent=eqs)
        elif eqs.is_Equivalent:
            if eqs.clue is None:
                if self.cond is eqs.lhs:
                    return eqs.rhs
        return eqs
    
    @property
    def plausible(self):
#         plausible = True, meaning, the statement is plausibly True, ready to be proven
#         plausible = False, meaning, the statement is proven False
#         plausible = None, meaning, the statement is proven True

        if 'plausible' in self._assumptions:
            return self._assumptions['plausible']

        if self.is_BooleanTrue:
            return 
        if self.is_BooleanFalse:
            return False

        equivalent = self.equivalent
        if equivalent is not None:
            if isinstance(equivalent, (tuple, list)):
                for parent in equivalent:
                    if parent.plausible:
                        return True
    
                return
            return equivalent.plausible
    
        given = self.given
        if given is not None:
            if isinstance(given, (tuple, list, set)):
                for parent in given:
                    assert parent is not self, self
                    if parent.plausible:
                        return True

                return
            if given.plausible is not None:
#             if self is given by a False / plausible proposition, then self is plausible
                return True
            return 
        
        imply = self.imply
        if imply is not None:
#             if self implies a False proposition, then self must be False
            plausible = imply._assumptions.get('plausible')
            if plausible is False:
                return False
            return True
        
        negation = self.negation
        if negation is not None:
            plausible = negation.plausible
            if plausible is True:
                return True
            if plausible is False:
                return
            return False

    @plausible.setter
    def plausible(self, value):
        if value:
            # this axiom is plausible to be true!
            if 'plausible' in self._assumptions:
                del self._assumptions['plausible']
        else:
            # this axiom is plausible to be false!
            self._assumptions['plausible'] = False

        equivalent = self.equivalent
        if equivalent is not None:
            self.equivalent = None
            process_equivalent(equivalent, value)
            return            

        imply = self.imply
        if imply is not None:
            self.imply = None
            process_imply(imply, value)
            return
        
        negation = self.negation
        if negation is not None:
            self.negation = None
            process_negation(negation, value)            
            return
        
        given = self.given
        if given is not None:
            self.given = None
            process_given(given, value)
            return

    def __neg__(self):
        cond = -self.cond
        return Inference(cond, equivalent=self)
    
    def doit(self, *args, **kwargs):
        cond = self.cond.doit(*args, **kwargs)
        return Inference(cond, equivalent=self)
    
    def __invert__(self):
        """Return the negated relationship.
        This works more or less identical to ``~``/``Not``. The difference is
        that ``negated`` returns the relationship even if `evaluate=False`.
        Hence, this is useful in code when checking for e.g. negated relations
        to exisiting ones as it will not be affected by the `evaluate` flag.
        """
        invert = self.cond.invert()
        limits_exists = self.cond.limits_exists()
        invert |= self.domain_definition().invert()
        
        if limits_exists:
            from sympy import Exists
            return Exists(invert, *limits_exists, negation=self).simplify()
        
        return Inference(invert, negation=self)

    def simplify(self, emplace=False):
        cond = self.cond.simplify()
        if cond != self.cond:
            if emplace:
                return Inference(cond, **self._assumptions)
            return Inference(cond, equivalent=self)
        return self
    
    def limits_subs(self, *args, **kwargs):
        cond = self.cond.limits_subs(*args, **kwargs)
        if cond != self.cond:
            return Inference(cond, equivalent=self)
        return self
    
    def subs(self, *args, **kwargs): 
        if 'simplify' not in kwargs:
            kwargs['simplify'] = True

        if all(eq.is_Equal for eq in args):
            for eq in args:
                old, new = eq.args
                 
                if self.plausible: 
                    if eq.plausible:
                        cond = self.cond._subs(old, new, **kwargs)
                        if cond == self.cond:
                            continue
                        self = Inference(cond, given=(self, eq))
                    else:
                        if self.is_Or:
                            eqs = []
                            for eq in self.args:
                                eqs.append(eq._subs(old, new) & eq.domain_definition())
                                
                            self = self.func(*eqs).copy(equivalent=self)
                        else:
                            cond = self.cond._subs(old, new, **kwargs)
                            if cond == self.cond:
                                continue

                            cond &= self.domain_definition()
                            self = Inference(cond, equivalent=self)                            
                else:
                    cond = self.cond._subs(old, new, **kwargs)
                    if cond == self.cond:
                        continue
                    
                    if eq.plausible:
                        self = Inference(cond, given=eq)
                    else:
                        self = Inference(cond, plausible=None)
                    
            return self 
            
        old, new = args
        if not old.is_symbol:
            return self
        
        new = sympify(new)        
        
        if self.plausible and new._has(old) and old.is_given is False: 
            # used in mathematical induction
            cond = self._subs(old, new, **kwargs)      
            return Inference(cond, plausible=True)
        
        if new in old.domain:
            if self.is_ConditionalBoolean:
                assert old not in self.variables, 'not supported in built-in axioms, please employ proved theorems: algebra.all.imply.cond.subs.apply(...)'
                function = self.function._subs(old, new, **kwargs)
                limits = []
                for x, *ab in self.limits:
                    if x.is_Indexed or x.is_Slice:
                        indices = tuple(index._subs(old, new, **kwargs) for index in x.indices)
                        if x.indices != indices:
                            x = x.func(x.base, *indices)
                    limits.append((x, *(e._subs(old, new, **kwargs) for e in ab)))
                       
                cond = self.func(function, *limits)
            else:
                cond = self._subs(old, new, **kwargs)
            return Inference(cond, given=self)
        
        domain = old.domain_bounded
        if domain is not None and new not in domain:
            if self.is_ForAll:
                from sympy import NotContains
                assert old not in self.variables, 'not supported in built-in axioms, please employ proved theorems: algebra.all.imply.ou.subs'
                function = self.function._subs(old, new) | NotContains(new, domain)
                cond = self.func(function, *self.limits)
            else:
                cond = self.forall((old,))
                old = old.unbounded
                if old != new:
                    cond = cond._subs(old, new, **kwargs)
        else:
            cond = self._subs(old, new, **kwargs)
            
        return Inference(cond, plausible=None)
    
    def set_clause(self, clue, eqs, force=False):
        if clue == 'equivalent':
            if force:
                self.equivalent = None
            self.equivalent = eqs
        elif clue == 'given':
            if force:
                self.given = None
            self.given = eqs
        elif clue == 'imply':
            if force:
                self.imply = None
            self.imply = eqs

    @property
    def reversed(self):
        return Inference(self.cond.reversed, equivalent=self)
    
    def forall(self, *limits, **kwargs):
        return Inference(self.cond.forall(*limits, **kwargs), equivalent=self)
    
    # return False or return the common given condition!
    def coexist_with(self, rhs):
        while self != rhs:
            if self.equivalent is None: 
                if self.given is None:
                    if rhs.equivalent is None:
                        if rhs.given is None:
                            return False
                        else:
                            rhs = rhs.given
                            if isinstance(rhs, list): 
                                return self.coexist_with_list(rhs)
                    else:
                        rhs = rhs.equivalent
                        if isinstance(rhs, list):
                            return self.coexist_with_list(rhs)
                    continue                        
                else:
                    self = self.given
            else:
                self = self.equivalent
                
            if isinstance(self, list):
                return rhs.coexist_with_list(self)
            
            if self == rhs:
                return self
            
            if rhs.equivalent is None: 
                if rhs.given is None:
                    continue
                else:
                    rhs = rhs.given
            else:
                rhs = rhs.equivalent
                
            if isinstance(rhs, list):
                return self.coexist_with_list(rhs)
            
        return self
    
    def coexist_with_list(self, rhs):
        eq_set = {*rhs}
        bases = [None] * len(rhs)
        
        def get_basis(i):
            if bases[i] is None:
                bases[i] = self.coexist_with(rhs[i])
            return bases[i]
        
        for i, eq in enumerate(rhs):
            basis = get_basis(i)
            if basis is False:
                continue
            
            eqs = plausibles(eq_set - {eq})
            if not eqs:
                return basis
            
            hit = True
            for j, eq in enumerate(rhs):
                if j == i:
                    continue
                basis_j = get_basis(j)
                if basis_j != basis:
                    hit = False
                    break
            if hit:
                return basis
        return False
    
    def __and__(self, other):
        if self.is_Exists and other.is_Exists and self.limits == other.limits:
            if self.coexist_with(other) is not False:
                    return self.func(self.function & other.function, *self.limits, equivalent=(self, other))
        return Inference(self.cond & other.cond, equivalent=(self, other))
    
    def __add__(self, other):
        if self.is_ConditionalBoolean:
            return self.this.function + other
        
        if isinstance(other, int):
            other = sympify(other)
        
        if self.is_Equal:
            if not other.is_Boolean and not other.is_set:
                return Inference(self.func(self.lhs + other, self.rhs + other), equivalent=self)
            if other.is_Relational:
                return Inference(other.func(self.lhs + other.lhs, self.rhs + other.rhs), equivalent=(self, other))
            
        elif self.is_Relational:
                 
            if not other.is_Boolean and not other.is_set:
                return Inference(self.func(self.lhs + other, self.rhs + other), equivalent=self)
            if other.is_Equal:
                return Inference(self.func(self.lhs + other.lhs, self.rhs + other.rhs), equivalent=(self, other))
            if self.func == other.func:
                return Inference(self.func(self.lhs + other.lhs, self.rhs + other.rhs), given=(self, other))
    
    def __rsub__(self, other):
        other = sympify(other)
        if self.is_Equal:
            assert not other.is_Relational 
            return self.func(other - self.lhs, other - self.rhs, equivalent=self).simplify()
    
    def __sub__(self, other):
        if self.is_ConditionalBoolean:
            return self.this.function - other
                
        if isinstance(other, int):
            other = sympify(other)
                    
        if self.is_Equal:
            if not other.is_Boolean and not other.is_set:
                return Inference(self.func(self.lhs - other, self.rhs - other), equivalent=self)
            if other.is_Relational:
                return Inference(other.func.reversed_type(self.lhs - other.lhs, self.rhs - other.rhs), equivalent=(self, other))
            
        elif self.is_Relational:
            if isinstance(other, int) or not other.is_Boolean and not other.is_set:
                return Inference(self.func(self.lhs - other, self.rhs - other), equivalent=self)
            if other.is_Equal:
                return Inference(self.func(self.lhs - other.lhs, self.rhs - other.rhs), equivalent=(self, other))
    
    def __pow__(self, other):
        if self.is_Equal:
            other = sympify(other)
            if other.is_positive:
                return self.func(self.lhs ** other, self.rhs ** other, given=self)
        elif self.is_ConditionalBoolean:
            return self.this.function * other
        
    def __mod__(self, other):
        other = sympify(other)
        assert other.is_integer
        if self.is_Equal: 
            return self.func(self.lhs % other, self.rhs % other, given=self)
        elif self.is_ConditionalBoolean:
            return self.this.function % other
            
    def __mul__(self, other):
        if self.is_ConditionalBoolean:
            return self.this.function * other
                
        if isinstance(other, int):
            other = sympify(other)
            
        if self.is_Equal:
            if other.is_Equal:
                if other.lhs.is_nonzero or other.rhs.is_nonzero:
                    return self.func(self.lhs * other.lhs, self.rhs * other.rhs, equivalent=(self, other))
                return self.func(self.lhs * other.lhs, self.rhs * other.rhs, given=(self, other))
                
            elif not other.is_Boolean and not other.is_set:
                if other.is_nonzero:
                    return self.func(self.lhs * other, self.rhs * other, equivalent=self)
                return self.func(self.lhs * other, self.rhs * other, given=self)
            
        if not other.is_Boolean:
            if self.is_Relational: 
                if other > 0:
                    return Inference(self.func(self.lhs * other, self.rhs * other), equivalent=self)
                if other < 0:
                    return Inference(self.func.reversed_type(self.lhs * other, self.rhs * other), equivalent=self)
                
        if self.is_Greater:
            if other.is_Greater:
                if self.rhs.is_extended_nonnegative: 
                    if other.rhs.is_extended_nonnegative:
                        return self.func(self.lhs * other.lhs, self.rhs * other.rhs, given=(self, other))
                if self.lhs.is_extended_nonpositive: 
                    if other.lhs.is_extended_nonpositive:
                        return self.reversed_type(self.lhs * other.lhs, self.rhs * other.rhs, given=(self, other))
        
    def __matmul__(self, rhs):
        if self.is_ConditionalBoolean:
            return self.this.function @ rhs
        
        if rhs.is_Equal:
            if rhs.lhs.is_invertible or rhs.rhs.is_invertible:
                return self.func(self.lhs @ rhs.lhs, self.rhs @ rhs.rhs, equivalent=(self, rhs))
            return self.func(self.lhs @ rhs.lhs, self.rhs @ rhs.rhs, given=(self, rhs))

        else: 
            assert not rhs.is_boolean
            if rhs.is_invertible:
                return self.func(self.lhs @ rhs, self.rhs @ rhs, equivalent=(self, rhs))
            return self.func(self.lhs @ rhs, self.rhs @ rhs, given=self)
            
    def __truediv__(self, other):
        if self.is_ConditionalBoolean:
            return self.this.function / other
        
        if isinstance(other, int):
            other = sympify(other)
                    
        if self.is_Relational: 
            if self.is_Equal:
                lhs = (self.lhs / other).ratsimp().simplify()
                rhs = (self.rhs / other).ratsimp().simplify()

                if other.is_nonzero:
                    return self.func(lhs, rhs, equivalent=self)
                from sympy import Or
                return Or(self.func(other, 0), self.func(lhs, rhs), equivalent=self)
                            
            if other.is_positive:
                return Inference(self.func(self.lhs / other, self.rhs / other), equivalent=self)
            if other.is_negative:
                return Inference(self.func.reversed_type(self.lhs / other, self.rhs / other), equivalent=self)
            
    def __getitem__(self, indices):
        if self.is_Equal: 
            if isinstance(indices, slice):
                x, *args = indices.start, indices.stop, indices.step
                if x is None or not x.is_symbol or args[1] is None and args[0].is_integer:
                    assert indices.step is None
                    start, stop = indices.start, indices.stop
                    size = self.lhs.shape[0]
                    assert self.lhs.shape == self.rhs.shape
                    assert start is None or start >= 0, "try to prove %s >= 0" % start
                    
                    if stop <= size:
                        ...
                    elif stop.is_symbol:
                        _stop = stop.definition
                        assert _stop is not None and _stop <= size, "try to prove %s <= %s" % (stop, size)
                    else:
                        raise Exception("try to prove %s <= %s" % (stop, size))
                    
                    return self.func(self.lhs[indices], self.rhs[indices], given=self)
                else:
                    if x.is_bounded:
                        x = x.unbounded
                    m = self.lhs.shape[0]
                    is_equivalent = False
                    if len(args) == 2:
                        if args[0] == 0 and args[1] == m:
                            is_equivalent = True
                    else:
                        assert len(args) == 1
                        if args[0] == m:
                            is_equivalent = True
                    if is_equivalent:
                        return self.func(self.lhs[x], self.rhs[x], equivalent=self)
                    else:
                        from sympy import ForAll
                        return ForAll(self.func(self.lhs[x], self.rhs[x]), (x, *args), given=self)
            return self.func(self.lhs[indices], self.rhs[indices], given=self)
        elif self.is_ConditionalBoolean:
            return self.this.function[indices]

    def is_equivalent_of(self, rhs):
        while True:
            if self == rhs:
                return True
            equivalent = self.equivalent
            if equivalent is None:
                return False
            
            if isinstance(equivalent, (list, tuple)):
                equivalent = plausibles(equivalent)                
                if len(equivalent) != 1:
                    return False
                equivalent, *_ = equivalent
            self = equivalent

    def is_given_by(self, given):
        while True:
            equivalent = equivalent_ancestor(self)
            if len(equivalent) != 1:
                return False
            equivalent, *_ = equivalent
            
            if equivalent is self:
                return False
            
            if isinstance(equivalent.given, (list, tuple)):
                for i, g in enumerate(equivalent.given):
                    if g is not given:
                        continue
                    if all(g.plausible is None for j, g in enumerate(equivalent.given) if j != i):
                        return True                    
            elif equivalent.given is given:
                return True
            
            self = equivalent
            
            
def equivalent_ancestor(a):
    if a is None:
        return a
    while True:
        equivalent = a.equivalent
        if equivalent is None:
            return {a}

        if isinstance(equivalent, (list, tuple)):
            res = set()
            for e in equivalent:
                if e.plausible:
                    res |= equivalent_ancestor(e)
            return res

        a = equivalent

            
from sympy.core.sympify import converter, sympify

converter[Inference] = lambda infer: infer.cond 

from sympy.core.assumptions import Operator
converter[Operator] = lambda op: op.basic

from sympy.core.core import Wanted
converter[Wanted] = lambda wanted: wanted

# converter[slice] = lambda s: s


def process_equivalent(equivalent, value):
    if value:
        if isinstance(equivalent, (list, tuple)):
            plausibility_array = plausibles(equivalent)
            if len(plausibility_array) == 1:
                plausibility_array[0].plausible = True
                return                 

            for eq in plausibility_array:
                eq.plausible = True
                
            return

        equivalent.plausible = True
        return 
    else:
        if isinstance(equivalent, (list, tuple)):
            plausibility_array = plausibles(equivalent)
            if len(plausibility_array) == 1:
                plausibility_false = plausibles_false(equivalent)
                if not plausibility_false:
                    plausibility_array[0].plausible = False
            else:
                given = {p.given for p in plausibility_array}
                if len(given) == 1:
                    given, *_ = given
                    if given is not None:
                        given.plausible = False
                    
        else:
            equivalent.plausible = False


def process_imply(imply, value):
    if value:
        if type(imply) == list:
            array = plausibles(imply)
            for eq in array:
                eq.plausible = True
            return

        if isinstance(imply.given, tuple):
#                 imply will be true unless all of imply.given is proven true!            
            if all(g.plausible is None for g in imply.given):
                imply.plausible = True
        else:
            imply.plausible = True


def process_negation(negation, value):
    plausible = negation.plausible
    if value:
        if plausible:
            negation.plausible = False
        else:
            assert plausible is False
    else:
        if plausible:
            negation.plausible = True
        else:
            assert plausible is None


def process_given(given, value):
    if value:
        if isinstance(given, (list, tuple)):
            plausibility_array = plausibles(given)
            if len(plausibility_array) == 1:
                return

            if len(plausibility_array) == 2:
                set_equivalence_relationship(*plausibility_array)
                return

            return

    else:
        if isinstance(given, (list, tuple, set)):
            plausibility_array = plausibles(given)
            if len(plausibility_array) == 1:
                plausibility_array[0].plausible = False
        else:
            given.plausible = False


def process_options(value=True, **kwargs):
    equivalent = kwargs.get('equivalent')
    if equivalent is not None:
        process_equivalent(equivalent, value)
        return        

    given = kwargs.get('given')
    if given is not None:
        process_given(given, value)
        return

    imply = kwargs.get('imply')
    if imply is not None:
        process_imply(imply, value)
        return
    
    negation = kwargs.get('negation')
    if negation is not None:
        process_negation(negation, value)
        return


def plausibles(parent):
    return [eq for eq in parent if eq.plausible]


def set_equivalence_relationship(lhs, rhs):
    if lhs.set_equivalence_relationship(rhs):
        return
    if rhs.set_equivalence_relationship(lhs):
        return


def plausibles_false(parent):
    return [eq for eq in parent if eq.plausible is False]

