"""
Boolean algebra module for SymPy
"""

from collections import defaultdict
from itertools import combinations, product
from sympy.core.add import Add
from sympy.core.basic import Basic
from sympy.core.cache import cacheit
from sympy.core.compatibility import (ordered, range, with_metaclass,
    as_int, is_sequence)
from sympy.core.function import Application, Derivative
from sympy.core.numbers import Number
from sympy.core.operations import LatticeOp
from sympy.core.singleton import Singleton, S
from sympy.core.sympify import converter, _sympify, sympify
from sympy.utilities.iterables import sift, ibin
from sympy.utilities.miscellany import filldedent
from sympy.logic.invoker import Invoker


def as_Boolean(e):
    """Like bool, return the Boolean value of an expression, e,
    which can be any instance of Boolean or bool.

    Examples
    ========

    >>> from sympy import true, false, nan
    >>> from sympy.logic.boolalg import as_Boolean
    >>> from sympy.abc import x
    >>> as_Boolean(0) is false
    True
    >>> as_Boolean(1) is true
    True
    >>> as_Boolean(x)
    x
    >>> as_Boolean(2)
    Traceback (most recent call last):
    ...
    TypeError: expecting bool or Boolean, not `2`.
    >>> as_Boolean(nan)
    Traceback (most recent call last):
    ...
    TypeError: expecting bool or Boolean, not `nan`.

    """
    from sympy.core.symbol import Symbol
    if e == True:
        return S.true
    if e == False:
        return S.false
    if isinstance(e, Symbol):
        z = e.is_zero
        if z is None:
            return e
        return S.false if z else S.true
    if isinstance(e, Boolean):
        return e
    raise TypeError('expecting bool or Boolean, not `%s`.' % e)


class Boolean(Basic):
    """A boolean object is an object for which logic operations make sense."""

    is_boolean = True
    __slots__ = ()

    def simplify_condition_on_random_variable(self):
        return self
        
    def sanctity_check(self, *limits):
        from sympy.concrete.expr_with_limits import limits_dict        
        for x, domain in limits_dict(limits).items():
            if isinstance(domain, list):
                continue
            if domain not in self.domain_defined(x):
                return False
        return True
        
    def simplify(self, deep=False, wrt=None):
        if wrt is not None:
            domain_defined = self.domain_defined(wrt)
            if domain_defined != wrt.domain:
                _wrt = wrt.copy(domain=domain_defined, **wrt._assumptions)
                this = self._subs(wrt, _wrt).simplify(deep=True)._subs(_wrt, wrt)
                if this != self: 
                    this.equivalent = self
                    return this
            return self
        
        if deep:
            hit = False
            args = []
            for arg in self.args: 
                _arg = arg.simplify(deep=deep)
                
                if _arg != arg:
                    hit = True
                args.append(_arg)
            if hit:
                return self.func(*args, equivalent=self).simplify()
        return self

    def apply(self, axiom, *args, **kwargs):
        eqs = axiom.apply(self, *args, **kwargs)
        if isinstance(eqs, list):
            eqs = And(*eqs, equivalent=eqs)
        elif eqs.is_Equivalent:
            if eqs.clue is None:
                if self is eqs.lhs:
                    return eqs.rhs
        return eqs

    @staticmethod
    def bfn(bfn, eq):
        function = bfn(eq.function)
        kwargs = {}
        if function is bfn.__self__:
            return function 
        if function.equivalent is not None:
            kwargs['equivalent'] = [bfn.__self__, eq]
            function.equivalent = None
        elif function.given is not None:
            kwargs['given'] = [bfn.__self__, eq]
            function.given = None

        return eq.func(function, *eq.limits, **kwargs).simplify()

    def forall(self, *limits, simplify=True):
        if len(limits) == 1:
            x, *args = limits[0]
            if not self._has(x): 
                return self
            from sympy import ForAll
            if len(args) == 2:
                from sympy.sets.sets import Interval
    
                domain = Interval(*args, integer=x.is_integer)
            elif len(args) == 1:
                domain = args[0]
                if not domain.is_set:
                    domain = x.domain_conditioned(domain)
            else:
                _x = x.unbounded
                self = ForAll(self._subs(x, _x), (_x, x.domain), equivalent=self)
                return self.simplify() if simplify else self
                
            x_domain = x.domain
            if domain == x_domain:
                if not simplify:
                    _x = x.unbounded
                    self = ForAll(self._subs(x, _x), (_x, x.domain), equivalent=self)
                    return self
        else:
            return
            for limit in limits:
                self = self.forall(limit, simplify=simplify)                

        return self

    def limits_exists(self):
        from sympy.tensor.indexed import Indexed, Slice
        from sympy.stats.rv import RandomSymbol
        free_symbols = {*self.free_symbols}
        for symbol in self.free_symbols:
            if symbol.is_given:
                free_symbols.discard(symbol)
                continue
                        
            if isinstance(symbol, (RandomSymbol, Indexed, Slice)):
                free_symbols -= symbol.free_symbols
                free_symbols.add(symbol)

        deletes = set()
        for y in free_symbols:
            deletes |= y.domain.free_symbols
            
        free_symbols -= deletes
        if free_symbols:
            return [(s,) for s in free_symbols]        
        
    def __invert__(self):
        """Return the negated relationship.

        Examples
        ========

        >>> from sympy import Eq
        >>> from sympy.abc import x
        >>> Eq(x, 1)
        Eq(x, 1)
        >>> ~_
        Ne(x, 1)
        >>> x < 1
        x < 1
        >>> ~_
        x >= 1

        Notes
        =====

        This works more or less identical to ``~``/``Not``. The difference is
        that ``negated`` returns the relationship even if `evaluate=False`.
        Hence, this is useful in code when checking for e.g. negated relations
        to exisiting ones as it will not be affected by the `evaluate` flag.
        """
        invert = self.invert()
        limits_exists = self.limits_exists()
        invert |= self.domain_definition().invert()
        
        if limits_exists:
            from sympy import Exists
            return Exists(invert, *limits_exists, counterpart=self).simplify()
        
        return invert.copy(counterpart=self)        

    def invert(self):
        return Boolean.__new__(self.invert_type, *self.args)

    def __new__(cls, *args, **kwargs):
        for name, value in [*kwargs.items()]:
            if value is None:
                del kwargs[name]
        return Basic.__new__(cls, *args, **kwargs)

    @property
    def this(self):
        return Invoker(self)

    def __rshift__(self, other):
        """Overloading for >>"""
        return Sufficient(self, other)

    def __lshift__(self, other):
        """Overloading for <<"""
        return Sufficient(other, self)

    __rrshift__ = __lshift__
    __rlshift__ = __rshift__

    def __xor__(self, other):
        return Xor(self, other)

    __rxor__ = __xor__

    def equals(self, other):
        """
        Returns True if the given formulas have the same truth table.
        For two formulas to be equal they must have the same literals.

        Examples
        ========

        >>> from sympy.abc import A, B, C
        >>> from sympy.logic.boolalg import And, Or, Not
        >>> (A >> B).equals(~B >> ~A)
        True
        >>> Not(And(A, B, C)).equals(And(Not(A), Not(B), Not(C)))
        False
        >>> Not(And(A, Not(A))).equals(Or(B, Not(B)))
        False
        """
        from sympy.logic.inference import satisfiable
        from sympy.core.relational import Relational

        if self.has(Relational) or other.has(Relational):
            raise NotImplementedError('handling of relationals')
        return self.atoms() == other.atoms() and \
            not satisfiable(Not(Equivalent(self, other)))

    def to_nnf(self, simplify=True):
        # override where necessary
        return self

    def as_set(self):
        """
        Rewrites Boolean expression in terms of real sets.

        Examples
        ========

        >>> from sympy import Symbol, Eq, Or, And
        >>> x = Symbol('x', real=True)
        >>> Eq(x, 0).as_set()
        {0}
        >>> (x > 0).as_set()
        Interval.open(0, oo)
        >>> And(-2 < x, x < 2).as_set()
        Interval.open(-2, 2)
        >>> Or(x < -2, 2 < x).as_set()
        Union(Interval.open(-oo, -2), Interval.open(2, oo))
        """
        from sympy.calculus.util import periodicity
        from sympy.core.relational import Relational
        free = self.free_symbols
        if len(free) == 1:
            x = free.pop()
            reps = {}
            for r in self.atoms(Relational):
                if periodicity(r, x) not in (0, None):
                    s = r._eval_as_set()
                    if s.is_EmptySet or s.is_UniversalSet or s == S.Reals:
                        reps[r] = s.as_relational(x)
                        continue
                    raise NotImplementedError(filldedent('''
                        as_set is not implemented for relationals
                        with periodic solutions
                        '''))
            return self.subs(reps)._eval_as_set()
        else:
            raise NotImplementedError("Sorry, as_set has not yet been"
                                      " implemented for multivariate"
                                      " expressions")

    @property
    def binary_symbols(self):
        from sympy.core.relational import Eq, Ne
        return set().union(*[i.binary_symbols for i in self.args if i.is_Boolean or i.is_Symbol or isinstance(i, (Eq, Ne))])

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

    @property
    def clue(self):
        if self.equivalent is not None:
            return 'equivalent'
        elif self.given is not None:
            return 'given'
        elif self.imply is not None:
            return 'imply'

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
                return True
            return 
        
        imply = self.imply
        if imply is not None: 
            return True
        
        counterpart = self.counterpart
        if counterpart is not None:
            plausible = counterpart.plausible
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

        given = self.given
        if given is not None:
            self.given = None
            process_given(given, value)
            return

        imply = self.imply
        if imply is not None:
            self.imply = None
            process_imply(imply, value)
            return

        counterpart = self.counterpart
        if counterpart is not None:
            self.counterpart = None
            plausible = counterpart.plausible
            if value:
                if plausible:
                    counterpart.plausible = False
                else:
                    assert plausible is False
            else:
                if plausible:
                    counterpart.plausible = True
                else:
                    assert plausible is None

    @property
    def equivalent(self):
        if 'equivalent' in self._assumptions:
            return self._assumptions['equivalent']

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

# here we define counterpart = counterproposition
    @property
    def counterpart(self):
        if 'counterpart' in self._assumptions:
            return self._assumptions['counterpart']

    @counterpart.setter
    def counterpart(self, eq):
        if eq is not None:
            assert 'counterpart' not in self._assumptions
            self._assumptions['counterpart'] = eq
            return

        if 'counterpart' in self._assumptions:
            del self._assumptions['counterpart']

    @property
    def derivative(self):
        if 'derivative' in self._assumptions:
            return self._assumptions['derivative']

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
                if isinstance(other, list):
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
                    if isinstance(equivalent, list):
                        p, *q = sorted((eq, *equivalent), key=default_sort_key)                    
                    else:
                        p, q = sorted((eq, equivalent), key=default_sort_key)
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
        if 'plausible' in self._assumptions:
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
                        yield from given.find_plausibles(is_equivalent)
                else:
                    yield from given.find_plausibles(is_equivalent)
        
    @derivative.setter
    def derivative(self, dic):
        if dic is not None:
            self._assumptions['derivative'] = dic
            return

        derivative = self.derivative
        if derivative is None:
            return

        if isinstance(derivative, list):
            if self.is_BinaryCondition or self.is_And or \
            self.is_ForAll and (self.function.is_Equality or self.function.is_And) or \
            self.is_Exists and self.function.is_Equality:
            # Exists of And structure is not deductive!
                if all(eq.plausible is None for eq in derivative):
                    del self._assumptions['derivative']
                    self.plausible = True
            return
        
    @property
    def given(self):
        if 'given' in self._assumptions:
            return self._assumptions['given']

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
        if 'imply' in self._assumptions:
            return self._assumptions['imply']

    @imply.setter
    def imply(self, eq):
        if eq is not None:
            assert self is not eq
            self._assumptions['imply'] = eq
            return

        if 'imply' in self._assumptions:
            del self._assumptions['imply']

    @property
    def dtype(self):
        from sympy.core.symbol import dtype
        return dtype.condition

    @property
    def shape(self): 
        return ()

    def overwrite(self, origin, **assumptions):
        if origin != self:
            for k, v in assumptions.items():
                self._assumptions[k] = v
            return self
        return origin

    def as_KroneckerDelta(self):
        ...

    def _eval_is_random(self):
        for arg in self.args:
            if arg.is_random:
                return True

    def induct(self, **kwargs):
        if self.given is not None:
            given = self.given
            if isinstance(given, list):
                given = And(*given)
                
            if kwargs.get('given'):
                return Sufficient(self, given)
            return Sufficient(given, self)
        if self.equivalent is not None:
            equivalent = self.equivalent
            if isinstance(equivalent, list):
                equivalent = And(*equivalent)
                
            if kwargs.get('given'):
                return Necessary(equivalent, self)
            
            if kwargs.get('imply', True):
                if kwargs.get('reverse'):
                    if self.plausible:
                        self._assumptions['plausible'] = True
                        equivalent.equivalent = self
                    
                    return Sufficient(self, equivalent)
                return Sufficient(equivalent, self)
            
            return Equivalent(equivalent, self)
        if self.imply is not None:
            imply = self.imply
            if isinstance(imply, list):
                imply = And(*imply)

            if kwargs.get('given'):
                return Necessary(imply, self)
                
            return Sufficient(self, imply)
        
    @property    
    def wrt(self):
        wrt, *_ = self.free_symbols
        return wrt

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

        
class BinaryCondition(Boolean):
    """Base class for all binary relation types.
    """
    __slots__ = ()
    
    @property
    def lhs(self):
        """The left-hand side of the relation."""
        return self._args[0]

    @property
    def rhs(self):
        """The right-hand side of the relation."""
        return self._args[1]

    @property
    def reversed(self):
        """Return the relationship with sides reversed.

        Examples
        ========

        >>> from sympy import Eq
        >>> from sympy.abc import x
        >>> Eq(x, 1)
        Eq(x, 1)
        >>> _.reversed
        Eq(1, x)
        >>> x < 1
        x < 1
        >>> _.reversed
        1 > x
        """
        a, b = self.args
        return self.reversed_type(b, a, equivalent=self, evaluate=False)

    def _eval_domain_defined(self, x):
        return self.lhs.domain_defined(x) & self.rhs.domain_defined(x)

    def domain_definition(self):
        eq = self.lhs.domain_definition() & self.rhs.domain_definition()
        eq.given = self
        return eq
    
    def __nonzero__(self):
        return False
    
    __bool__ = __nonzero__
    
    @staticmethod
    def eval(cls, *args, **options):
        args = list(map(sympify, args))
        from sympy.core.parameters import global_parameters
        evaluate = options.pop('evaluate', global_parameters.evaluate)
        
        if evaluate:
            evaluated = cls.eval(*args)
            if evaluated is not None:

                if options and evaluated.is_BooleanAtom:
                    if 'plausible' in options:
                        if evaluated:
                            del options['plausible']
                        else:
                            options['plausible'] = False
                    else:
                        return evaluated.copy(**options)
                else:
                    return evaluated

        return BinaryCondition.__new__(cls, *args, **options)
    
    def bisect(self, *args, **kwargs):
        if len(args) == 1:
            eq = args[0]
            if not isinstance(eq, slice) and eq.is_boolean:
                from sympy import ForAll
                wrt = kwargs.get('wrt')
                if wrt is None:
                    wrt = eq.wrt
                if wrt.is_given:
                    _eq = eq.invert()
                    return And(Or(eq, self), Or(_eq, self), equivalent=self)
                else:
                    if wrt.is_bounded:
                        self = self.forall((wrt,), simplify=False)
                    else:
                        self = ForAll(self.copy(equivalent=None), (wrt,), equivalent=self)
                    assert self.function is not self.equivalent
                    assert self.is_ForAll
                    return self.bisect(wrt.domain_conditioned(eq))
                                        
        lhs = self.lhs.bisect(*args, **kwargs)
        rhs = self.rhs.bisect(*args, **kwargs)
        if lhs.is_BlockMatrix and rhs.is_BlockMatrix:
            return And(*[self.func(lhs, rhs) for lhs, rhs in zip(lhs.args, rhs.args)], equivalent=self)
#             eqs = []
#             for lhs, rhs in zip(lhs.args, rhs.args):
#                 eq = self.func(lhs, rhs)
#                 if lhs.is_LAMBDA:
#                     eq = Or(eq, lhs.domain_definition().invert().simplify())
#                 if rhs.is_LAMBDA:
#                     eq = Or(eq, rhs.domain_definition().invert().simplify())
#                 eqs.append(eq)  
#             return And(*eqs, equivalent=self)
                
        return self

    @property
    def wrt(self):
        free_symbols = self.lhs.free_symbols
        if not free_symbols:
            free_symbols = self.rhs.free_symbols
        wrt, *_ = free_symbols
        return wrt
    
    def subs(self, *args, **kwargs):
        old, new = args
        if not old.is_symbol:
            return self
        new = sympify(new)
        
        if self.plausible:
            lhs, rhs = self.lhs._subs(old, new), self.rhs._subs(old, new)
            if new._has(old):
                assumptions = {'plausible': True}
            else:
                assumptions = {'given': self}
            eq = self.func(lhs, rhs, **assumptions)
            if not new._has(old):
                return eq
            return eq
        else:
            if new in old.domain:
                lhs = self.lhs._subs(old, new)
                rhs = self.rhs._subs(old, new)            
                return self.func(lhs, rhs, given=self)
            
            domain = old.domain_bounded
            if domain is not None and new not in domain:
                self = self.forall((old,))
                old = old.unbounded
                if old != new:
                    self = self.subs(old, new)
                return self

            return self.func(self.lhs._subs(*args, **kwargs).simplify(), self.rhs._subs(*args, **kwargs).simplify())
 
    
def plausibles(parent):
    return [eq for eq in parent if eq.plausible]


def plausibles_false(parent):
    return [eq for eq in parent if eq.plausible is False]


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


def _relationship(lhs, rhs):
    if lhs is rhs:
        return 'equivalent'
    
    equivalent = rhs.equivalent
    if equivalent is None:
        given = rhs.given
        if given is not None:
            if isinstance(given, (list, tuple)):
                for rhs in given:
                    if _relationship(lhs, rhs):
                        return 'given'
            else:
                if _relationship(lhs, given):
                    return 'given'           
    
    elif isinstance(equivalent, (list, tuple)):
        for rhs in equivalent:
            clue = _relationship(lhs, rhs)
            if clue:
                return clue
    else:
        clue = _relationship(lhs, equivalent)
        if clue:
            return clue

    
# lhs.equivalent.equivalent[0].equivalent[0].equivalent[1].given is rhs.equivalent.equivalent[0].equivalent.equivalent[1].given.given.equivalent.equivalent[1]    
def relationship(lhs, rhs):
    if lhs is rhs:
        return 'equivalent'

    equivalent = lhs.equivalent
    if equivalent is None:
        given = lhs.given
        
        if given is not None:
            if isinstance(given, (list, tuple)):
                for lhs in given:
                    if relationship(lhs, rhs):
                        return 'given'
            else:
                if relationship(given, rhs):
                    return 'given'
                
    elif isinstance(equivalent, (list, tuple)):
        for lhs in equivalent:
            clue = relationship(lhs, rhs)
            if clue:
                return clue
    
    else:
        clue = relationship(equivalent, rhs)
        if clue:
            return clue
        
    return _relationship(lhs, rhs)

    
def given_ancestor(a):
    if a is None:
        return a
    while True:
        given = a.equivalent
        if given is None:
            given = a.given

        if given is None:
            return {a}

        if isinstance(given, (list, tuple)):
            res = set()
            for e in given:
                if e.plausible:
                    res |= given_ancestor(e)
            return res

        a = given


def set_equivalence_relationship(lhs, rhs):
    if lhs.set_equivalence_relationship(rhs):
        return
    if rhs.set_equivalence_relationship(lhs):
        return


def process_equivalent(equivalent, value):
    if value:
        if isinstance(equivalent, list):
            plausibility_array = plausibles(equivalent)
            if len(plausibility_array) == 1:
                plausibility_array[0].plausible = True
                return                 

            for eq in plausibility_array:
                eq.plausible = True
                
            return
            if len(plausibility_array) == 2:
                set_equivalence_relationship(*plausibility_array)
                return
            return

        equivalent.plausible = True
        return 
    else:
        if isinstance(equivalent, list):
            plausibility_array = plausibles(equivalent)
            if len(plausibility_array) == 1:
                plausibility_false = plausibles_false(equivalent)
                if not plausibility_false:
                    plausibility_array[0].plausible = False
        else:
            equivalent.plausible = False


def process_imply(imply, value):
    if value:
        if type(imply) == list:
            array = plausibles(imply)
            for eq in array:
                eq.plausible = True
            return

        imply.plausible = True
    else: 
        if imply.plausible is None:
            derivative = imply.derivative
            
            if any(eq.plausible is None for eq in derivative):
                return 
            
            plausibles = [eq for eq in derivative if eq.plausible]
            if len(plausibles) == 1:
                imply.derivative = None
                plausibles[0].plausible = True
        elif imply.plausible:
            derivative = imply.derivative
            if derivative is None:
                return
            
            if any(eq.plausible is None for eq in derivative):
                imply.plausible = None
            elif all(eq.plausible is False for eq in derivative):
                imply.plausible = False


def process_given(given, value):
    if value:
        if isinstance(given, (list, tuple)):
            plausibility_array = plausibles(given)
            if len(plausibility_array) == 1:
#                 plausibility_array[0].plausible = True
                print('evidence is not sufficient for deduction')
                return

            if len(plausibility_array) == 2:
                set_equivalence_relationship(*plausibility_array)
                return

            return

        given.derivative = None
    else:
        if isinstance(given, (list, tuple, set)):
            plausibility_array = plausibles(given)
            if len(plausibility_array) == 1:
                plausibility_array[0].plausible = False
        else:
            given.plausible = False


def process_options(equivalent=None, given=None, imply=None, value=True, **_):

    if equivalent is not None:
        process_equivalent(equivalent, value)
        return        

    if given is not None:
        process_given(given, value)
        return

    if imply is not None:
        process_imply(imply, value)
        return


class BooleanAtom(Boolean):
    """
    Base class of BooleanTrue and BooleanFalse.
    """
#     is_Boolean = True
    is_Atom = True
    _op_priority = 11  # higher than Expr

    def simplify(self, *a, **kw):
        return self

    def expand(self, *a, **kw):
        return self

    @property
    def canonical(self):
        return self

    def _noop(self, other=None):
        raise TypeError('BooleanAtom not allowed in this context.')

    __add__ = _noop
    __radd__ = _noop
    __sub__ = _noop
    __rsub__ = _noop
    __mul__ = _noop
    __rmul__ = _noop
    __pow__ = _noop
    __rpow__ = _noop
    __rdiv__ = _noop
    __truediv__ = _noop
    __div__ = _noop
    __rtruediv__ = _noop
    __mod__ = _noop
    __rmod__ = _noop
    _eval_power = _noop

    # /// drop when Py2 is no longer supported
    def __lt__(self, other):
        from sympy.utilities.miscellany import filldedent
        raise TypeError(filldedent('''
            A Boolean argument can only be used in
            Eq and Ne; all other relationals expect
            real expressions.
        '''))

    __le__ = __lt__
    __gt__ = __lt__
    __ge__ = __lt__


    # \\\

class BooleanTrue(with_metaclass(Singleton, BooleanAtom)):
    """
    SymPy version of True, a singleton that can be accessed via S.true.

    This is the SymPy version of True, for use in the logic module. The
    primary advantage of using true instead of True is that shorthand boolean
    operations like ~ and >> will work as expected on this class, whereas with
    True they act bitwise on 1. Functions in the logic module will return this
    class when they evaluate to true.

    Notes
    =====

    There is liable to be some confusion as to when ``True`` should
    be used and when ``S.true`` should be used in various contexts
    throughout SymPy. An important thing to remember is that
    ``sympify(True)`` returns ``S.true``. This means that for the most
    part, you can just use ``True`` and it will automatically be converted
    to ``S.true`` when necessary, similar to how you can generally use 1
    instead of ``S.One``.

    The rule of thumb is:

    "If the boolean in question can be replaced by an arbitrary symbolic
    ``Boolean``, like ``Or(x, y)`` or ``x > 1``, use ``S.true``.
    Otherwise, use ``True``"

    In other words, use ``S.true`` only on those contexts where the
    boolean is being used as a symbolic representation of truth.
    For example, if the object ends up in the ``.args`` of any expression,
    then it must necessarily be ``S.true`` instead of ``True``, as
    elements of ``.args`` must be ``Basic``. On the other hand,
    ``==`` is not a symbolic operation in SymPy, since it always returns
    ``True`` or ``False``, and does so in terms of structural equality
    rather than mathematical, so it should return ``True``. The assumptions
    system should use ``True`` and ``False``. Aside from not satisfying
    the above rule of thumb, the assumptions system uses a three-valued logic
    (``True``, ``False``, ``None``), whereas ``S.true`` and ``S.false``
    represent a two-valued logic. When in doubt, use ``True``.

    "``S.true == True is True``."

    While "``S.true is True``" is ``False``, "``S.true == True``"
    is ``True``, so if there is any doubt over whether a function or
    expression will return ``S.true`` or ``True``, just use ``==``
    instead of ``is`` to do the comparison, and it will work in either
    case.  Finally, for boolean flags, it's better to just use ``if x``
    instead of ``if x is True``. To quote PEP 8:

    Don't compare boolean values to ``True`` or ``False``
    using ``==``.

    * Yes:   ``if greeting:``
    * No:    ``if greeting == True:``
    * Worse: ``if greeting is True:``

    Examples
    ========

    >>> from sympy import sympify, true, false, Or
    >>> sympify(True)
    True
    >>> _ is True, _ is true
    (False, True)

    >>> Or(true, false)
    True
    >>> _ is true
    True

    Python operators give a boolean result for true but a
    bitwise result for True

    >>> ~true, ~True
    (False, -2)
    >>> true >> true, True >> True
    (True, 0)

    Python operators give a boolean result for true but a
    bitwise result for True

    >>> ~true, ~True
    (False, -2)
    >>> true >> true, True >> True
    (True, 0)

    See Also
    ========
    sympy.logic.boolalg.BooleanFalse

    """

    def __nonzero__(self):
        return True

    __bool__ = __nonzero__

    def __hash__(self):
        return hash(True)

    def invert(self):
        return S.false

    def as_set(self):
        """
        Rewrite logic operators and relationals in terms of real sets.

        Examples
        ========

        >>> from sympy import true
        >>> true.as_set()
        UniversalSet
        """
        from sympy import UniversalSet
        return UniversalSet()

    def copy(self, **kwargs):
        if kwargs:
            return BooleanTrueAssumption(**kwargs)
        return self

    def overwrite(self, _, **assumptions):
        return self.copy(**assumptions)        

    def domain_conditioned(self, x):
        return x.domain

    
class BooleanFalse(with_metaclass(Singleton, BooleanAtom)):
    """
    SymPy version of False, a singleton that can be accessed via S.false.

    This is the SymPy version of False, for use in the logic module. The
    primary advantage of using false instead of False is that shorthand boolean
    operations like ~ and >> will work as expected on this class, whereas with
    False they act bitwise on 0. Functions in the logic module will return this
    class when they evaluate to false.

    Notes
    ======
    See note in :py:class`sympy.logic.boolalg.BooleanTrue`

    Examples
    ========

    >>> from sympy import sympify, true, false, Or
    >>> sympify(False)
    False
    >>> _ is False, _ is false
    (False, True)

    >>> Or(true, false)
    True
    >>> _ is true
    True

    Python operators give a boolean result for false but a
    bitwise result for False

    >>> ~false, ~False
    (True, -1)
    >>> false >> false, False >> False
    (True, 0)

    See Also
    ========
    sympy.logic.boolalg.BooleanTrue

    """

    def __nonzero__(self):
        return False

    __bool__ = __nonzero__

    def __hash__(self):
        return hash(False)

    def invert(self):
        return S.true

    def as_set(self):
        """
        Rewrite logic operators and relationals in terms of real sets.

        Examples
        ========

        >>> from sympy import false
        >>> false.as_set()
        EmptySet()
        """
        from sympy import EmptySet 
        return EmptySet()

    def copy(self, **kwargs):
        assert self.equivalent is None
        if kwargs:
            return BooleanFalseAssumption(**kwargs)
        return self

    def overwrite(self, _, **assumptions):
        return self.copy(**assumptions)        

    def domain_conditioned(self, x):
        return x.emptySet


class BooleanFalseAssumption(BooleanAtom):
    is_BooleanFalse = True

    def __nonzero__(self):
        return False

    __bool__ = __nonzero__

    def __new__(cls, **kwargs):
#         assert S.BooleanFalse.equivalent is None
        if kwargs:
            return Boolean.__new__(cls, **kwargs)        
        return S.BooleanFalse

    def _latex(self, _):
        return r"\text{%s}" % False

    def invert(self):
        return S.true


class BooleanTrueAssumption(BooleanAtom):
    is_BooleanTrue = True

    def __nonzero__(self):
        return True

    __bool__ = __nonzero__

    def __new__(cls, **kwargs):
        if kwargs:
            return Boolean.__new__(cls, **kwargs)
        return S.BooleanTrue

    def _latex(self, _):
        return r"\text{%s}" % True

    def invert(self):
        return S.false


true = BooleanTrue()
false = BooleanFalse()
# We want S.true and S.false to work, rather than S.BooleanTrue and
# S.BooleanFalse, but making the class and instance names the same causes some
# major issues (like the inability to import the class directly from this
# file).
S.true = true
S.false = false

converter[bool] = lambda x: S.true if x else S.false


class BooleanFunction(Application, Boolean):
    """Boolean function is a function that lives in a boolean space
    It is used as base class for And, Or, Not, etc.
    """

    def __new__(cls, *args, **assumptions):
        if len(args) == 1 and isinstance(args[0], frozenset):
            _args = args[0]
        else:
            _args = args
        return Application.__new__(cls, *args, **assumptions)

    def __bool__(self):
        return False

    @property
    def dtype(self):
        from sympy.core.symbol import dtype
        return dtype.condition

    def _eval_simplify(self, ratio, measure, rational, inverse):
        rv = self.func(*[a._eval_simplify(ratio=ratio, measure=measure,
                                          rational=rational, inverse=inverse)
                         for a in self.args])
        return simplify_logic(rv)

#     def simplify(self, ratio=1.7, measure=count_ops, rational=False,
#                  inverse=False):
#         return self._eval_simplify(ratio, measure, rational, inverse)

    # /// drop when Py2 is no longer supported
    def __lt__(self, other):
        from sympy.utilities.miscellany import filldedent
        raise TypeError(filldedent('''
            A Boolean argument can only be used in
            Eq and Ne; all other relationals expect
            real expressions.
        '''))

    __le__ = __lt__
    __ge__ = __lt__
    __gt__ = __lt__

    # \\\

    @classmethod
    def binary_check_and_simplify(self, *args):
        from sympy.core.relational import Relational, Eq, Ne
        args = [as_Boolean(i) for i in args]
        binary_symbols = set().union(*[i.binary_symbols for i in args])
        rel = set().union(*[i.atoms(Relational) for i in args])
        reps = {}
        for x in binary_symbols:
            for r in rel:
                if x in binary_symbols and x in r.free_symbols:
                    if isinstance(r, (Eq, Ne)):
                        if not (
                                S.true in r.args or
                                S.false in r.args):
                            reps[r] = S.false
                    else:
                        raise TypeError(filldedent('''
                            Incompatible use of binary symbol `%s` as a
                            real variable in `%s`
                            ''' % (x, r)))
        for index, i in enumerate(args):
            for x, y in reps.items():
                i = i._subs(x, y)
            args[index] = i
        return args
#         return [i.subs(reps) for i in args]

    def to_nnf(self, simplify=True):
        return self._to_nnf(*self.args, simplify=simplify)

    @classmethod
    def _to_nnf(cls, *args, **kwargs):
        simplify = kwargs.get('simplify', True)
        argset = set([])
        for arg in args:
            if not is_literal(arg):
                arg = arg.to_nnf(simplify)
            if simplify:
                if isinstance(arg, cls):
                    arg = arg.args
                else:
                    arg = (arg,)
                for a in arg:
                    if Not(a) in argset:
                        return cls.zero
                    argset.add(a)
            else:
                argset.add(arg)
        return cls(*argset)

    # the diff method below is copied from Expr class
    def diff(self, *symbols, **assumptions):
        assumptions.setdefault("evaluate", True)
        return Derivative(self, *symbols, **assumptions)

    def _eval_derivative(self, x):
        from sympy.core.relational import Eq
        from sympy.functions.elementary.piecewise import Piecewise
        if x in self.binary_symbols:
            return Piecewise(
                (0, Eq(self.subs(x, 0), self.subs(x, 1))),
                (1, True))
        elif x in self.free_symbols:
            # not implemented, see https://www.encyclopediaofmath.org/
            # index.php/Boolean_differential_calculus
            pass
        else:
            return S.Zero

    def _apply_patternbased_simplification(self, rv, patterns, measure,
                                           dominatingvalue,
                                           replacementvalue=None):
        """
        Replace patterns of Relational

        Parameters
        ==========

        rv : Expr
            Boolean expression

        patterns : tuple
            Tuple of tuples, with (pattern to simplify, simplified pattern)

        measure : function
            Simplification measure

        dominatingvalue : boolean or None
            The dominating value for the function of consideration.
            For example, for And S.false is dominating. As soon as one
            expression is S.false in And, the whole expression is S.false.

        replacementvalue : boolean or None, optional
            The resulting value for the whole expression if one argument
            evaluates to dominatingvalue.
            For example, for Nand S.false is dominating, but in this case
            the resulting value is S.true. Default is None. If replacementvalue
            is None and dominatingvalue is not None,
            replacementvalue = dominatingvalue
        """
        from sympy.core.relational import Relational, _canonical
        if replacementvalue is None and dominatingvalue is not None:
            replacementvalue = dominatingvalue
        # Use replacement patterns for Relationals
        changed = True
        Rel, nonRel = sift(rv.args, lambda i: isinstance(i, Relational),
                           binary=True)
        if len(Rel) <= 1:
            return rv
        Rel, nonRealRel = sift(rv.args, lambda i: all(s.is_real is not False
                                                      for s in i.free_symbols),
                               binary=True)
        Rel = [i.canonical for i in Rel]
        while changed and len(Rel) >= 2:
            changed = False
            # Sort based on ordered
            Rel = list(ordered(Rel))
            # Create a list of possible replacements
            results = []
            # Try all combinations
            for ((i, pi), (j, pj)) in combinations(enumerate(Rel), 2):
                for k, (pattern, simp) in enumerate(patterns):
                    res = []
                    # use SymPy matching
                    oldexpr = rv.func(pi, pj)
                    tmpres = oldexpr.match(pattern)
                    if tmpres:
                        res.append((tmpres, oldexpr))
                    # Try reversing first relational
                    # This and the rest should not be required with a better
                    # canonical
                    oldexpr = rv.func(pi.reversed, pj)
                    tmpres = oldexpr.match(pattern)
                    if tmpres:
                        res.append((tmpres, oldexpr))
                    # Try reversing second relational
                    oldexpr = rv.func(pi, pj.reversed)
                    tmpres = oldexpr.match(pattern)
                    if tmpres:
                        res.append((tmpres, oldexpr))
                    # Try reversing both relationals
                    oldexpr = rv.func(pi.reversed, pj.reversed)
                    tmpres = oldexpr.match(pattern)
                    if tmpres:
                        res.append((tmpres, oldexpr))

                    if res:
                        for tmpres, oldexpr in res:
                            # we have a matching, compute replacement
                            np = simp.subs(tmpres)
                            if np == dominatingvalue:
                                # if dominatingvalue, the whole expression
                                # will be replacementvalue
                                return replacementvalue
                            # add replacement
                            if not isinstance(np, ITE):
                                # We only want to use ITE replacements if
                                # they simplify to a relational
                                costsaving = measure(oldexpr) - measure(np)
                                if costsaving > 0:
                                    results.append((costsaving, (i, j, np)))
            if results:
                # Sort results based on complexity
                results = list(reversed(sorted(results,
                                               key=lambda pair: pair[0])))
                # Replace the one providing most simplification
                cost, replacement = results[0]
                i, j, newrel = replacement
                # Remove the old relationals
                del Rel[j]
                del Rel[i]
                if dominatingvalue is None or newrel != ~dominatingvalue:
                    # Insert the new one (no need to insert a value that will
                    # not affect the result)
                    Rel.append(newrel)
                # We did change something so try again
                changed = True

        rv = rv.func(*([_canonical(i) for i in ordered(Rel)]
                     +nonRel + nonRealRel))
        return rv

    def _eval_domain_defined(self, x):
        domain = Boolean._eval_domain_defined(self, x)
        for arg in self.args:
            domain &= arg.domain_defined(x)
        return domain


class And(LatticeOp, BooleanFunction):
    """
    Logical AND function.

    It evaluates its arguments in order, giving False immediately
    if any of them are False, and True if they are all True.

    Examples
    ========

    >>> from sympy.core import symbols
    >>> from sympy.abc import x, y
    >>> from sympy.logic.boolalg import And
    >>> x & y
    x & y

    Notes
    =====

    The ``&`` operator is provided as a convenience, but note that its use
    here is different from its normal use in Python, which is bitwise
    and. Hence, ``And(a, b)`` and ``a & b`` will return different things if
    ``a`` and ``b`` are integers.

    >>> And(x, y).subs(x, 1)
    y

    """

    def _print_LogOp(self, args, char):

        arg = args[0]
        if arg.is_Or:
            tex = r"\left(%s\right)" % self._print(arg)
        else:
            tex = r"%s" % self._print(arg)

        for arg in args[1:]:
            if arg.is_Boolean and not arg.is_Not:
                tex += r" %s \left(%s\right)" % (char, self._print(arg))
            else:
                tex += r" %s %s" % (char, self._print(arg))

        return tex

    def _sympystr(self, p):
        from sympy.printing.precedence import PRECEDENCE
#         \N{LOGICAL AND}
        return p.stringify(self.args, " & ", PRECEDENCE["BitwiseAnd"])

    def _latex(self, p):
        if len(self.args) == 2:
            strict_less_than, strict_greater_than = self.args
            if strict_less_than.is_StrictLessThan and strict_greater_than.is_StrictGreaterThan:
                if strict_less_than.lhs == strict_greater_than.lhs:
                    a, x, b = strict_greater_than.rhs, strict_less_than.lhs, strict_less_than.rhs
                    a = p._print(a)
                    b = p._print(b)
                    x = p._print(x)
                    return r"%s \lt %s \lt %s" % (a, x, b)
        args = []
        for arg in self.args:
            if arg.is_Or or arg.is_Conditioned:
                args.append(r"\left(%s\right)" % p._print(arg))
            else:
                args.append(p._print(arg))

        return r"\wedge ".join(args)

    def invert(self):
        return self.invert_type(*(arg.invert() for arg in self.args))

    def apply(self, *axiom, split=True, **kwargs): 
        if split:
            if len(axiom) > 1:
                eqs = []
                for eq, axiom in zip(self.args, axiom): 
                    eqs.append(eq.apply(axiom, **kwargs))
                return self.func(*eqs, given=self)

            from sympy.concrete.conditional_boolean import ConditionalBoolean
            axiom = axiom[0]
            args = []
            funcs = []
            
            depth = kwargs.pop('depth', None)
            if depth is None:
                for eq in self.args:
                    if eq.is_ConditionalBoolean:
                        func, function = eq.funcs()
                        funcs = ConditionalBoolean.merge_func(funcs, func)
                        args.append(function)
                    else:
                        args.append(eq)
            elif depth == 0:
                args = [*self.args]
            else:
                def instantiate(eq):
                    function = eq
                    for i in range(depth):
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
        else:
            return Boolean.apply(self, *axiom, **kwargs)

    def subs(self, *args, **kwargs):
        if all(isinstance(arg, Boolean) for arg in args):
            result = LatticeOp.subs(self, *args, **kwargs)
            if result.is_BooleanAtom:
                result = result.copy(equivalent=[self, *args])
            else:
                result.equivalent = [self, *args]
            return result
                
        old, new = args
        new = sympify(new)
        if self.plausible:
            eqs = [eq._subs(old, new) for eq in self.args]
            return self.func(*eqs, plausible=True)
        else:
            result = self._subs(old, new)
            if result.is_BooleanAtom:
                result = result.copy(equivalent=self)
            else:
                result.equivalent = self
        
            return result
        return self

    def __new__(cls, *args, **options):
        valuable = set()
        for arg in args:
            if arg:
                continue            
            if arg.is_BooleanFalse:
                return arg.copy(**options)
            valuable.add(arg)

        args = valuable
        if len(args) == 0:
            return S.BooleanTrue.copy(**options)
        if len(args) == 1:
            eq, *_ = args
            return eq.func(*eq.args, **options)

        if set(v.invert() for v in args) & args:
#             assert S.BooleanFalse.equivalent is None
            return S.BooleanFalse.copy(**options)

        return LatticeOp.__new__(cls, *args, **options)

    zero = false
    
    identity = S.true

    nargs = None

    @classmethod
    def _new_args_filter(cls, args):
        newargs = []
        rel = []
#         args = BooleanFunction.binary_check_and_simplify(*args)
        for x in reversed(args):
            if x.is_Relational:
                c = x.canonical
                if c in rel:
                    continue
                nc = c.invert()
                nc = nc.canonical
                if any(r == nc for r in rel):
                    return [S.false]
                rel.append(c)
            newargs.append(x)
        return LatticeOp._new_args_filter(newargs, And)

    def _eval_simplify(self, ratio, measure, rational, inverse):
        from sympy.core.relational import Equality, Relational
        from sympy.solvers.solveset import linear_coeffs
        # standard simplify
        rv = super(And, self)._eval_simplify(
            ratio, measure, rational, inverse)
        if not isinstance(rv, And):
            return rv
        # simplify args that are equalities involving
        # symbols so x == 0 & x == y -> x==0 & y == 0
        Rel, nonRel = sift(rv.args, lambda i: isinstance(i, Relational),
                           binary=True)
        if not Rel:
            return rv
        eqs, other = sift(Rel, lambda i: isinstance(i, Equality), binary=True)
        if not eqs:
            return rv
        reps = {}
        sifted = {}
        if eqs:
            # group by length of free symbols
            sifted = sift(ordered([
                (i.free_symbols, i) for i in eqs]),
                lambda x: len(x[0]))
            eqs = []
            while 1 in sifted:
                for free, e in sifted.pop(1):
                    x = free.pop()
                    if e.lhs != x or x in e.rhs.free_symbols:
                        try:
                            m, b = linear_coeffs(
                                e.rewrite(Add, evaluate=False), x)
                            enew = e.func(x, -b / m)
                            if measure(enew) <= ratio * measure(e):
                                e = enew
                            else:
                                eqs.append(e)
                                continue
                        except ValueError:
                            pass
                    if x in reps:
                        eqs.append(e.func(e.rhs, reps[x]))
                    else:
                        reps[x] = e.rhs
                        eqs.append(e)
                resifted = defaultdict(list)
                for k in sifted:
                    for f, e in sifted[k]:
                        e = e.subs(reps)
                        f = e.free_symbols
                        resifted[len(f)].append((f, e))
                sifted = resifted
        for k in sifted:
            eqs.extend([e for f, e in sifted[k]])
        other = [ei.subs(reps) for ei in other]
        rv = rv.func(*([i.canonical for i in (eqs + other)] + nonRel))
        patterns = simplify_patterns_and()
        return self._apply_patternbased_simplification(rv, patterns,
                                                       measure, False)

    def _eval_as_set(self):
        from sympy.sets.sets import Intersection
        return Intersection(*[arg.as_set() for arg in self.args])

    def split(self, *args, **kwargs):
        eqs = [eq.func(*eq.args, given=self) for eq in self.args]
        if self.plausible:
            self.derivative = eqs
        return eqs

    def simplify(self, deep=False):
        dict_contains = defaultdict(set)        
        dict_notcontains = defaultdict(set)
        dict_domain = defaultdict(set)
        for eq in self._argset:
            if eq.is_Contains:
                e, S = eq.args
                dict_contains[e].add(eq)
            elif eq.is_NotContains:
                e, S = eq.args
                dict_notcontains[e].add(eq)
            elif eq.is_Inequality:
                x, y = eq.args
                dict_domain[x].add(eq)
                
        from sympy.sets import Intersection, Contains, NotContains, Union
        for e, eqs in dict_contains.items(): 
            if len(eqs) > 1: 
                sets = [contains.rhs for contains in eqs] 
                contains = Contains(e, Intersection(*sets))
                argset = self._argset - eqs
                return self.func(*argset, contains, equivalent=self)
            if e in dict_notcontains:
                _eqs = dict_notcontains[e]
                sets = [contains.rhs for contains in eqs]
                _sets = [contains.rhs for contains in _eqs]
                contains = Contains(e, Intersection(*sets) - Union(*_sets))                
                argset = self._argset - eqs - _eqs
                return self.func(*argset, contains, equivalent=self)                
                
        for e, eqs in dict_notcontains.items(): 
            if len(eqs) > 1: 
                sets = [contains.rhs for contains in eqs] 
                eq = NotContains(e, Union(*sets))
                argset = self._argset - eqs
                return self.func(*argset, eq, equivalent=self)
                            
        for e, eqs in dict_domain.items(): 
            if len(eqs) > 1:
                argset = self._argset - eqs
                eq, *eqs = eqs
                eq &= And(*eqs)
                if eq.is_And:
                    return self
                if eq.is_Contains:
                    return self
                return self.func(*argset, eq, equivalent=self).simplify()
                            
        return self

    def as_KroneckerDelta(self):
        eq = 1
        for c in self.args:
            e = c.as_KroneckerDelta()
            if e is None:
                return
            eq *= e
        return eq

    def __and__(self, other):
        """Overloading for & operator"""
        lhs = tuple(self._argset)
        
        rhs = None
        if other.is_And:
            rhs = tuple(other._argset)
        elif other.is_Or:
            _self = self.invert()
            if _self in other._argset:
                args = set(other._argset)
                args.remove(_self)
                rhs = (other.func(*args),)

        if rhs is None:
            rhs = (other,)

        return And(*lhs + rhs, equivalent=[self, other])

    def domain_conditioned(self, x):
        sol = x.domain
        for eq in self.args:
            sol &= x.domain_conditioned(eq)
        return sol

    @classmethod
    def simplify_ForAll(cls, self, function, *limits):
        res = self.simplify_int_limits(function)
        if res:
            function, limits = res
            return self.func(function, *limits, equivalent=self).simplify()
        
        limits_condition = self.limits_condition
        if limits_condition.is_And:
            limits_condition = limits_condition._argset
        else:
            limits_condition = {limits_condition}
        for i, eq in enumerate(function.args):
            if eq in limits_condition:
                args = [*function.args]
                del args[i]
                function = cls(*args)
                return self.func(function, *limits, equivalent=self).simplify()

    @classmethod
    def rewrite_from_Or(cls, self):
        for i, eq in enumerate(self.args):
            if isinstance(eq, cls):
                args = [*self.args]
                del args[i]
                this = self.func(*args)
                return cls(*((arg | this).simplify() for arg in eq.args), equivalent=self)
        
    def copy(self, **kwargs):
        obj = Basic.__new__(self.func, self._argset, **kwargs)
        obj._argset = self._argset
        return obj

    def bisect(self, *args, **kwargs):
        return self

    def collect(self, term):
        matched = []
        unmatch = []
        for eq in self.args:
            if eq.is_Or:
                if term in eq.args:
                    matched.append(Or(*eq._argset - {term}))
                    continue
            elif eq == term:
                matched.append(S.false)
                continue
            unmatch.append(eq)
        if unmatch: 
            return self.func(*unmatch, Or(term, self.func(*matched)), equivalent=self)            
        return Or(term, self.func(*matched), equivalent=self)
                
        
class Or(LatticeOp, BooleanFunction):
    """
    Logical OR function

    It evaluates its arguments in order, giving True immediately
    if any of them are True, and False if they are all False.

    Examples
    ========

    >>> from sympy.core import symbols
    >>> from sympy.abc import x, y
    >>> from sympy.logic.boolalg import Or
    >>> x | y
    x | y

    Notes
    =====

    The ``|`` operator is provided as a convenience, but note that its use
    here is different from its normal use in Python, which is bitwise
    or. Hence, ``Or(a, b)`` and ``a | b`` will return different things if
    ``a`` and ``b`` are integers.

    >>> Or(x, y).subs(x, 0)
    y

    """
    zero = true
    
    identity = S.false

    def _latex(self, p):
        return p._print_LogOp(self.args, r"\vee")

    def _sympystr(self, p):
        from sympy.printing.precedence import PRECEDENCE
#         \N{LOGICAL OR}        
        return p.stringify(self.args, " | ", PRECEDENCE["BitwiseOr"])

    def __new__(cls, *args, **options):
        valuable = set()
        for arg in args:
            if arg.is_BooleanFalse:
                continue
            if arg:
                return S.BooleanTrue.copy(**options)
            valuable.add(arg)

        if not valuable:
            return S.BooleanFalse.copy(**options)
        
        args = valuable
        if len(args) == 1:
            eq, *_ = args
            return eq.func(*eq.args, **options)

        if set(v.invert() for v in args) & args:
            if 'plausible' in options:
                del options['plausible']
            else:
                return S.BooleanTrue.copy(**options)

        return LatticeOp.__new__(cls, *args, **options)

    def invert(self):
        return self.invert_type(*(arg.invert() for arg in self.args))

    @classmethod
    def _new_args_filter(cls, args):
        newargs = []
        rel = []
#         args = BooleanFunction.binary_check_and_simplify(*args)
        for x in args:
            if x.is_Relational:
                c = x.canonical
                if c in rel:
                    continue
                nc = c.invert().canonical
                if any(r == nc for r in rel):
                    return [S.true]
                rel.append(c)
            newargs.append(x)
        return LatticeOp._new_args_filter(newargs, Or)

    def _eval_as_set(self):
        from sympy.sets.sets import Union
        return Union(*[arg.as_set() for arg in self.args])

    def _eval_simplify(self, ratio, measure, rational, inverse):
        # standard simplify
        rv = super(Or, self)._eval_simplify(ratio, measure, rational, inverse)
        if not isinstance(rv, Or):
            return rv
        patterns = simplify_patterns_or()
        return self._apply_patternbased_simplification(rv, patterns,
                                                       measure, S.true)

    def simplify(self, deep=False, **kwargs):
        if deep:
            return Boolean.simplify(self, deep, **kwargs)
        
        return self

    def split(self, *args, **kwargs):
        args = [arg.func(*arg.args, imply=self) for arg in self.args]        
        self.derivative = args
        return args

    def as_KroneckerDelta(self):
        eq = 1
        for c in self.args:
            e = c.as_KroneckerDelta()
            if e is None:
                return
            eq *= 1 - e
        return 1 - eq

    def subs(self, *args, **kwargs):
        if len(args) == 1:
            eq = args[0]
            if eq.is_ConditionalBoolean:
                return self.bfn(self.subs, eq)
            
            if eq.is_Equal:
                old, new = eq.args
                if self.plausible:
                    eqs = []
                    for eq in self.args:
                        eqs.append(eq._subs(old, new) & eq.domain_definition())
                    return self.func(*eqs).copy(equivalent=self)
                else:
                    eq = self._subs(old, new)                
                    return eq.copy(equivalent=self)
        old, new = args
        if old.is_given:
            return self
        result = LatticeOp.subs(self, *args, **kwargs)
        if all(isinstance(arg, Boolean) for arg in args): 
            result = result.copy(equivalent=[self, *args])            
        else: 
            result = result.copy(equivalent=self)
            
        return result

    def __and__(self, other):
        this = self
        if not other.is_Or:
            for eq in self._argset:
                if (other & eq).is_BooleanFalse:
                    args = set(self._argset)
                    args.remove(eq)
                    this = self.func(*args)
                    break

        if other.is_And:
            rhs = tuple(other._argset)
        else:
            rhs = (other,)

        return And(this, *rhs, equivalent=[self, other])

    def _eval_domain_defined(self, x):
        domain = x.emptySet
        for arg in self.args:
            domain |= arg.domain_defined(x)
        return domain

    def domain_conditioned(self, x):
        sol = x.emptySet
        for eq in self.args:
            sol |= x.domain_conditioned(eq)
        return x.domain & sol

    def bisect(self, eq, **kwargs):
        if eq.is_boolean:
            from sympy import ForAll
            wrt = kwargs.get('wrt')
            if wrt is None:
                wrt, *_ = eq.lhs.free_symbols
            if wrt.is_given:
                _eq = eq.invert()
                return And(Or(eq, self), Or(_eq, self), equivalent=self)                
            if wrt.is_bounded:
                self = self.forall((wrt,), simplify=False)
            else:
                self = ForAll(self, (wrt,), equivalent=self)
            assert self.is_ForAll
            return self.bisect(wrt.domain_conditioned(eq))
        return self

    @classmethod
    def rewrite_from_And(cls, self):
        for i, eq in enumerate(self.args):
            if isinstance(eq, cls):
                args = [*self.args]
                del args[i]
                this = self.func(*args)
                return cls(*((arg & this).simplify() for arg in eq.args), equivalent=self)

    @classmethod
    def rewrite_from_Sufficient(cls, self):
        p, q = self.args
        return cls(p.invert(), q, equivalent=self)
            
    @classmethod
    def rewrite_from_Necessary(cls, self):
        p, q = self.args
        return cls(p, q.invert(), equivalent=self)
    
    def copy(self, **kwargs):
        obj = Basic.__new__(self.func, self._argset, **kwargs)
        obj._argset = self._argset
        return obj

    def collect(self, term):
        matched = []
        unmatch = []
        for eq in self.args:
            if eq.is_And:
                if term in eq.args:
                    matched.append(Or(*eq._argset - {term}))
                    continue
            elif eq == term:
                matched.append(S.true)
                continue
            
            unmatch.append(eq)
        if unmatch: 
            return self.func(*unmatch, Or(term, self.func(*matched)), equivalent=self)            
        return And(term, self.func(*matched), equivalent=self)

    
And.invert_type = Or
Or.invert_type = And


class Not(BooleanFunction):
    """
    Logical Not function (negation)


    Returns True if the statement is False
    Returns False if the statement is True

    Examples
    ========

    >>> from sympy.logic.boolalg import Not, And, Or
    >>> from sympy.abc import x, A, B
    >>> Not(True)
    False
    >>> Not(False)
    True
    >>> Not(And(True, False))
    True
    >>> Not(Or(True, False))
    False
    >>> Not(And(And(True, x), Or(x, False)))
    ~x
    >>> ~x
    ~x
    >>> Not(And(Or(A, B), Or(~A, ~B)))
    ~((A | B) & (~A | ~B))

    Notes
    =====

    - The ``~`` operator is provided as a convenience, but note that its use
      here is different from its normal use in Python, which is bitwise
      not. In particular, ``~a`` and ``Not(a)`` will be different if ``a`` is
      an integer. Furthermore, since bools in Python subclass from ``int``,
      ``~True`` is the same as ``~1`` which is ``-2``, which has a boolean
      value of True.  To avoid this issue, use the SymPy boolean types
      ``true`` and ``false``.

    >>> from sympy import true
    >>> ~True
    -2
    >>> ~true
    False

    """

    @classmethod
    def eval(cls, arg):
        from sympy import (
            Equality, GreaterThan, LessThan,
            StrictGreaterThan, StrictLessThan, Unequality)
        if isinstance(arg, Number) or arg in (True, False):
            return false if arg else true
        if arg.is_Not:
            return arg.args[0]
        # Simplify Relational objects.
        if isinstance(arg, Equality):
            return Unequality(*arg.args)
        if isinstance(arg, Unequality):
            return Equality(*arg.args)
        if isinstance(arg, StrictLessThan):
            return GreaterThan(*arg.args)
        if isinstance(arg, StrictGreaterThan):
            return LessThan(*arg.args)
        if isinstance(arg, LessThan):
            return StrictGreaterThan(*arg.args)
        if isinstance(arg, GreaterThan):
            return StrictLessThan(*arg.args)

    def _eval_as_set(self):
        """
        Rewrite logic operators and relationals in terms of real sets.

        Examples
        ========

        >>> from sympy import Not, Symbol
        >>> x = Symbol('x')
        >>> Not(x > 0).as_set()
        Interval(-oo, 0)
        """
        return self.args[0].as_set().complement(S.Reals)

    def to_nnf(self, simplify=True):
        if is_literal(self):
            return self

        expr = self.args[0]

        func, args = expr.func, expr.args

        if func == And:
            return Or._to_nnf(*[~arg for arg in args], simplify=simplify)

        if func == Or:
            return And._to_nnf(*[~arg for arg in args], simplify=simplify)

        if func == Sufficient:
            a, b = args
            return And._to_nnf(a, ~b, simplify=simplify)

        if func == Equivalent:
            return And._to_nnf(Or(*args), Or(*[~arg for arg in args]),
                               simplify=simplify)

        if func == Xor:
            result = []
            for i in range(1, len(args) + 1, 2):
                for neg in combinations(args, i):
                    clause = [~s if s in neg else s for s in args]
                    result.append(Or(*clause))
            return And._to_nnf(*result, simplify=simplify)

        if func == ITE:
            a, b, c = args
            return And._to_nnf(Or(a, ~c), Or(~a, ~b), simplify=simplify)

        raise ValueError("Illegal operator %s in expression" % func)


class Xor(BooleanFunction):
    """
    Logical XOR (exclusive OR) function.


    Returns True if an odd number of the arguments are True and the rest are
    False.

    Returns False if an even number of the arguments are True and the rest are
    False.

    Examples
    ========

    >>> from sympy.logic.boolalg import Xor
    >>> from sympy import symbols
    >>> x, y = symbols('x y')
    >>> Xor(True, False)
    True
    >>> Xor(True, True)
    False
    >>> Xor(True, False, True, True, False)
    True
    >>> Xor(True, False, True, False)
    False
    >>> x ^ y
    Xor(x, y)

    Notes
    =====

    The ``^`` operator is provided as a convenience, but note that its use
    here is different from its normal use in Python, which is bitwise xor. In
    particular, ``a ^ b`` and ``Xor(a, b)`` will be different if ``a`` and
    ``b`` are integers.

    >>> Xor(x, y).subs(y, 0)
    x

    """

    def __new__(cls, *args, **kwargs):
        argset = set([])
        obj = super(Xor, cls).__new__(cls, *args, **kwargs)
        for arg in obj._args:
            if isinstance(arg, Number) or arg in (True, False):
                if arg:
                    arg = true
                else:
                    continue
            if isinstance(arg, Xor):
                for a in arg.args:
                    argset.remove(a) if a in argset else argset.add(a)
            elif arg in argset:
                argset.remove(arg)
            else:
                argset.add(arg)
        rel = [(r, r.canonical, (~r).canonical)
               for r in argset if r.is_Relational]
        odd = False  # is number of complimentary pairs odd? start 0 -> False
        remove = []
        for i, (r, c, nc) in enumerate(rel):
            for j in range(i + 1, len(rel)):
                rj, cj = rel[j][:2]
                if cj == nc:
                    odd = ~odd
                    break
                elif cj == c:
                    break
            else:
                continue
            remove.append((r, rj))
        if odd:
            argset.remove(true) if true in argset else argset.add(true)
        for a, b in remove:
            argset.remove(a)
            argset.remove(b)
        if len(argset) == 0:
            return false
        elif len(argset) == 1:
            return argset.pop()
        elif True in argset:
            argset.remove(True)
            return Not(Xor(*argset))
        else:
            obj._args = tuple(ordered(argset))
            obj._argset = frozenset(argset)
            return obj

    @property
    @cacheit
    def args(self):
        return tuple(ordered(self._argset))

    def to_nnf(self, simplify=True):
        args = []
        for i in range(0, len(self.args) + 1, 2):
            for neg in combinations(self.args, i):
                clause = [~s if s in neg else s for s in self.args]
                args.append(Or(*clause))
        return And._to_nnf(*args, simplify=simplify)

    def _eval_simplify(self, ratio, measure, rational, inverse):
        # as standard simplify uses simplify_logic which writes things as
        # And and Or, we only simplify the partial expressions before using
        # patterns
        rv = self.func(*[a._eval_simplify(ratio=ratio, measure=measure,
                                          rational=rational, inverse=inverse)
                       for a in self.args])
        if not isinstance(rv, Xor):  # This shouldn't really happen here
            return rv
        patterns = simplify_patterns_xor()
        return self._apply_patternbased_simplification(rv, patterns,
                                                       measure, None)


class Nand(BooleanFunction):
    """
    Logical NAND function.

    It evaluates its arguments in order, giving True immediately if any
    of them are False, and False if they are all True.

    Returns True if any of the arguments are False
    Returns False if all arguments are True

    Examples
    ========

    >>> from sympy.logic.boolalg import Nand
    >>> from sympy import symbols
    >>> x, y = symbols('x y')
    >>> Nand(False, True)
    True
    >>> Nand(True, True)
    False
    >>> Nand(x, y)
    ~(x & y)

    """

    @classmethod
    def eval(cls, *args):
        return Not(And(*args))


class Nor(BooleanFunction):
    """
    Logical NOR function.

    It evaluates its arguments in order, giving False immediately if any
    of them are True, and True if they are all False.

    Returns False if any argument is True
    Returns True if all arguments are False

    Examples
    ========

    >>> from sympy.logic.boolalg import Nor
    >>> from sympy import symbols
    >>> x, y = symbols('x y')

    >>> Nor(True, False)
    False
    >>> Nor(True, True)
    False
    >>> Nor(False, True)
    False
    >>> Nor(False, False)
    True
    >>> Nor(x, y)
    ~(x | y)

    """

    @classmethod
    def eval(cls, *args):
        return Not(Or(*args))


class Xnor(BooleanFunction):
    """
    Logical XNOR function.

    Returns False if an odd number of the arguments are True and the rest are
    False.

    Returns True if an even number of the arguments are True and the rest are
    False.

    Examples
    ========

    >>> from sympy.logic.boolalg import Xnor
    >>> from sympy import symbols
    >>> x, y = symbols('x y')
    >>> Xnor(True, False)
    False
    >>> Xnor(True, True)
    True
    >>> Xnor(True, False, True, True, False)
    False
    >>> Xnor(True, False, True, False)
    True

    """

    @classmethod
    def eval(cls, *args):
        return Not(Xor(*args))

       
class Sufficient(BinaryCondition):
    """
    Logical implication.

    A is Sufficient for B is equivalent to !A v B

    Accepts two Boolean arguments; A and B.
    Returns False if A is True and B is False
    Returns True otherwise.

    Examples
    ========

    >>> from sympy.logic.boolalg import Sufficient
    >>> from sympy import symbols
    >>> x, y = symbols('x y')

    >>> Sufficient(True, False)
    False
    >>> Sufficient(False, False)
    True
    >>> Sufficient(True, True)
    True
    >>> Sufficient(False, True)
    True
    >>> x >> y
    Sufficient(x, y)
    >>> y << x
    Sufficient(x, y)

    Notes
    =====

    The ``>>`` and ``<<`` operators are provided as a convenience, but note
    that their use here is different from their normal use in Python, which is
    bit shifts. Hence, ``Sufficient(a, b)`` and ``a >> b`` will return different
    things if ``a`` and ``b`` are integers.  In particular, since Python
    considers ``True`` and ``False`` to be integers, ``True >> True`` will be
    the same as ``1 >> 1``, i.e., 0, which has a truth value of False.  To
    avoid this issue, use the SymPy objects ``true`` and ``false``.

    >>> from sympy import true, false
    >>> True >> False
    1
    >>> true >> false
    False

    """

    def __new__(cls, *args, **assumptions):
        return BinaryCondition.eval(cls, *args, **assumptions)

    @classmethod
    def eval(cls, *args):
        try:
            newargs = []
            for x in args:
                if isinstance(x, Number) or x in (0, 1):
                    newargs.append(True if x else False)
                else:
                    newargs.append(x)
            A, B = newargs
        except ValueError:
            raise ValueError(
                "%d operand(s) used for an Sufficient "
                "(pairs are required): %s" % (len(args), str(args)))
        if B.is_BooleanFalse:
            return A.invert()
        if A.is_BooleanTrue:
            return B
        if A.is_BooleanFalse or B.is_BooleanTrue or A == B or A.is_And and B in A._argset:
            return S.true
        
        if A.is_Relational and B.is_Relational:
            if A.canonical == B.canonical:
                return S.true
            if A.invert().canonical == B.canonical:
                return B

    def to_nnf(self, simplify=True):
        a, b = self.args
        return Or._to_nnf(~a, b, simplify=simplify)

    def _sympystr(self, p): 
        return "%s \N{RIGHTWARDS DOUBLE ARROW} %s" % (p._print(self.lhs), p._print(self.rhs))
    
    def _latex(self, p, altchar='\Rightarrow'):
        A = p.conditions_wrapper(self.lhs)
        B = p.conditions_wrapper(self.rhs)
        return "%s %s %s" % (A, altchar, B)

    def __and__(self, other):
        """Overloading for & operator"""
        if other.is_Sufficient:
            if self.lhs == other.lhs:
                return self.func(self.lhs, self.rhs & other.rhs, equivalent=[self, other])
            if self.lhs == other.rhs:
                if self.rhs == other.lhs:
                    return Equivalent(self.lhs, self.rhs, equivalent=[self, other])
                
        elif other.is_Necessary:
            if self.lhs == other.lhs:
                if self.rhs == other.rhs:
                    return Equivalent(self.lhs, self.rhs, equivalent=[self, other])
                 
        return BinaryCondition.__and__(self, other)

    def split(self, *args, **kwargs):
        if self.rhs.is_And:
            eqs = [self.func(self.lhs, eq, given=self) for eq in self.rhs.args]    
        elif self.lhs.is_Or:
            eqs = [self.func(eq, self.rhs, given=self) for eq in self.lhs.args]
        else:
            return self
        if self.plausible:
            self.derivative = eqs
        return eqs


class Necessary(BinaryCondition):
    """
    Logical implication.

    A is Necessary for B is equivalent to A v !B

    Accepts two Boolean arguments; A and B.
    Returns False if A is True and B is False
    Returns True otherwise.

    """

    def __new__(cls, *args, **assumptions):
        return BinaryCondition.eval(cls, *args, **assumptions)

    @classmethod
    def eval(cls, *args):
        try:
            newargs = []
            for x in args:
                if isinstance(x, Number) or x in (0, 1):
                    newargs.append(True if x else False)
                else:
                    newargs.append(x)
            B, A = newargs
        except ValueError:
            raise ValueError(
                "%d operand(s) used for an Sufficient "
                "(pairs are required): %s" % (len(args), str(args)))
        if A == True or A == False or B == True or B == False:
            return Or(Not(A), B)
        elif A == B:
            return S.true
        elif A.is_Relational and B.is_Relational:
            if A.canonical == B.canonical:
                return S.true
            if A.invert().canonical == B.canonical:
                return B

    def to_nnf(self, simplify=True):
        b, a = self.args
        return Or._to_nnf(a.invert(), b, simplify=simplify)

    def _sympystr(self, p): 
        return "%s \N{LEFTWARDS DOUBLE ARROW} %s" % (p._print(self.lhs), p._print(self.rhs))

    def _latex(self, p):
        return Sufficient._latex(self, p, '\Leftarrow')

    def __and__(self, other):
        """Overloading for & operator"""
        if other.is_Sufficient:
            if self.lhs == other.lhs:
                if self.rhs == other.rhs:
                    return Equivalent(self.lhs, self.rhs, equivalent=[self, other])

        return BinaryCondition.__and__(self, other)

    def split(self, *args, **kwargs):
        if self.rhs.is_Or:
            eqs = [self.func(self.lhs, eq, given=self) for eq in self.rhs.args]    
        elif self.lhs.is_And:
            eqs = [self.func(eq, self.rhs, given=self) for eq in self.lhs.args]
        else:
            return self
        if self.plausible:
            self.derivative = eqs
        return eqs


class Equivalent(BinaryCondition):
    """
    Equivalence relation.

    Equivalent(A, B) is True iff A and B are both True or both False

    Returns True if all of the arguments are logically equivalent.
    Returns False otherwise.

    Examples
    ========

    >>> from sympy.logic.boolalg import Equivalent, And
    >>> from sympy.abc import x, y
    >>> Equivalent(False, False, False)
    True
    >>> Equivalent(True, False, False)
    False
    >>> Equivalent(x, And(x, True))
    True
    """

    def __new__(cls, *args, **options):
        from sympy.core.relational import Relational
        args = [_sympify(arg) for arg in args]

        argset = set(args)
        for x in args:
            if isinstance(x, Number) or x in [True, False]:  # Includes 0, 1
                argset.discard(x)
                argset.add(True if x else False)
        rel = []
        for r in argset:
            if isinstance(r, Relational):
                rel.append((r, r.canonical, r.invert().canonical))
        remove = []
        for i, (r, c, nc) in enumerate(rel):
            for j in range(i + 1, len(rel)):
                rj, cj = rel[j][:2]
                if cj == nc:
                    return false
                elif cj == c:
                    remove.append((r, rj))
                    break
        for a, b in remove:
            argset.remove(a)
            argset.remove(b)
            argset.add(True)
        if len(argset) <= 1:
            return S.true.copy(**options)
        if True in argset:
            argset.discard(True)
            return And(*argset)
        if False in argset:
            argset.discard(False)
            return And(*[arg.invert() for arg in argset])
        return super(Equivalent, cls).__new__(cls, *args, **options)

    def to_nnf(self, simplify=True):
        args = []
        for a, b in zip(self.args, self.args[1:]):
            args.append(Or(~a, b))
        args.append(Or(~self.args[-1], self.args[0]))
        return And._to_nnf(*args, simplify=simplify)

    def _sympystr(self, p): 
        return "%s \N{LEFT RIGHT DOUBLE ARROW} %s" % (p._print(self.lhs), p._print(self.rhs))

    def _latex(self, p):
        return Sufficient._latex(self, p, '\Leftrightarrow')

       
class Insufficient(BinaryCondition):

    def __new__(cls, *args, **assumptions):
        return BinaryCondition.eval(cls, *args, **assumptions)

    @classmethod
    def eval(cls, *args):
        ...
        
    def _sympystr(self, p): 
        return "%s \N{RIGHTWARDS DOUBLE ARROW WITH STROKE} %s" % (p._print(self.lhs), p._print(self.rhs))
    
    def _latex(self, p):
        A = p.conditions_wrapper(self.lhs)
        B = p.conditions_wrapper(self.rhs)
        return r"%s \nRightarrow %s" % (A, B)

    def __and__(self, other):
        return BinaryCondition.__and__(self, other)


class Unnecessary(BinaryCondition):
    
    @classmethod
    def eval(cls, *args):
        ...

    def _sympystr(self, p): 
        return "%s \N{LEFTWARDS DOUBLE ARROW WITH STROKE} %s" % (p._print(self.lhs), p._print(self.rhs))

    def _latex(self, p):
        return Sufficient._latex(self, p, '\nLeftarrow')


class Inequivalent(BinaryCondition):

    def _sympystr(self, p): 
        return "%s \N{LEFT RIGHT DOUBLE ARROW WITH STROKE} %s" % (p._print(self.lhs), p._print(self.rhs))

    def _latex(self, p):
        return Sufficient._latex(self, p, '\nLeftrightarrow')


Sufficient.reversed_type = Necessary
Necessary.reversed_type = Sufficient
Equivalent.reversed_type = Equivalent

Insufficient.reversed_type = Unnecessary
Unnecessary.reversed_type = Insufficient
Inequivalent.reversed_type = Inequivalent

Sufficient.invert_type = Insufficient
Necessary.invert_type = Unnecessary
Equivalent.invert_type = Inequivalent

Insufficient.invert_type = Sufficient 
Unnecessary.invert_type = Necessary
Inequivalent.invert_type = Equivalent


class ITE(BooleanFunction):
    """
    If then else clause.

    ITE(A, B, C) evaluates and returns the result of B if A is true
    else it returns the result of C. All args must be Booleans.

    Examples
    ========

    >>> from sympy.logic.boolalg import ITE, And, Xor, Or
    >>> from sympy.abc import x, y, z
    >>> ITE(True, False, True)
    False
    >>> ITE(Or(True, False), And(True, True), Xor(True, True))
    True
    >>> ITE(x, y, z)
    ITE(x, y, z)
    >>> ITE(True, x, y)
    x
    >>> ITE(False, x, y)
    y
    >>> ITE(x, y, y)
    y

    Trying to use non-Boolean args will generate a TypeError:

    >>> ITE(True, [], ())
    Traceback (most recent call last):
    ...
    TypeError: expecting bool, Boolean or ITE, not `[]`

    """

    def __new__(cls, *args, **kwargs):
        from sympy.core.relational import Eq, Ne
        if len(args) != 3:
            raise ValueError('expecting exactly 3 args')
        a, b, c = args
        # check use of binary symbols
        if isinstance(a, (Eq, Ne)):
            # in this context, we can evaluate the Eq/Ne
            # if one arg is a binary symbol and the other
            # is true/false
            b, c = map(as_Boolean, (b, c))
            binary_symbols = set().union(*[i.binary_symbols for i in (b, c)])
            if len(set(a.args) - binary_symbols) == 1:
                # one arg is a binary_symbols
                _a = a
                if a.lhs is S.true:
                    a = a.rhs
                elif a.rhs is S.true:
                    a = a.lhs
                elif a.lhs is S.false:
                    a = ~a.rhs
                elif a.rhs is S.false:
                    a = ~a.lhs
                else:
                    # binary can only equal True or False
                    a = S.false
                if isinstance(_a, Ne):
                    a = ~a
        else:
            a, b, c = BooleanFunction.binary_check_and_simplify(
                a, b, c)
        rv = None
        if kwargs.get('evaluate', True):
            rv = cls.eval(a, b, c)
        if rv is None:
            rv = BooleanFunction.__new__(cls, a, b, c, evaluate=False)
        return rv

    @classmethod
    def eval(cls, *args):
        from sympy.core.relational import Eq, Ne
        # do the args give a singular result?
        a, b, c = args
        if isinstance(a, (Ne, Eq)):
            _a = a
            if S.true in a.args:
                a = a.lhs if a.rhs is S.true else a.rhs
            elif S.false in a.args:
                a = ~a.lhs if a.rhs is S.false else ~a.rhs
            else:
                _a = None
            if _a is not None and isinstance(_a, Ne):
                a = ~a
        if a is S.true:
            return b
        if a is S.false:
            return c
        if b == c:
            return b
        else:
            # or maybe the results allow the answer to be expressed
            # in terms of the condition
            if b is S.true and c is S.false:
                return a
            if b is S.false and c is S.true:
                return Not(a)
        if [a, b, c] != args:
            return cls(a, b, c, evaluate=False)

    def to_nnf(self, simplify=True):
        a, b, c = self.args
        return And._to_nnf(Or(~a, b), Or(a, c), simplify=simplify)

    def _eval_as_set(self):
        return self.to_nnf().as_set()

    def _eval_rewrite_as_Piecewise(self, *args, **kwargs):
        from sympy.functions import Piecewise
        return Piecewise((args[1], args[0]), (args[2], True))

# end class definitions. Some useful methods


def conjuncts(expr):
    """Return a list of the conjuncts in the expr s.

    Examples
    ========

    >>> from sympy.logic.boolalg import conjuncts
    >>> from sympy.abc import A, B
    >>> conjuncts(A & B)
    frozenset({A, B})
    >>> conjuncts(A | B)
    frozenset({A | B})

    """
    return And.make_args(expr)


def disjuncts(expr):
    """Return a list of the disjuncts in the sentence s.

    Examples
    ========

    >>> from sympy.logic.boolalg import disjuncts
    >>> from sympy.abc import A, B
    >>> disjuncts(A | B)
    frozenset({A, B})
    >>> disjuncts(A & B)
    frozenset({A & B})

    """
    return Or.make_args(expr)


def distribute_and_over_or(expr):
    """
    Given a sentence s consisting of conjunctions and disjunctions
    of literals, return an equivalent sentence in CNF.

    Examples
    ========

    >>> from sympy.logic.boolalg import distribute_and_over_or, And, Or, Not
    >>> from sympy.abc import A, B, C
    >>> distribute_and_over_or(Or(A, And(Not(B), Not(C))))
    (A | ~B) & (A | ~C)
    """
    return _distribute((expr, And, Or))


def distribute_or_over_and(expr):
    """
    Given a sentence s consisting of conjunctions and disjunctions
    of literals, return an equivalent sentence in DNF.

    Note that the output is NOT simplified.

    Examples
    ========

    >>> from sympy.logic.boolalg import distribute_or_over_and, And, Or, Not
    >>> from sympy.abc import A, B, C
    >>> distribute_or_over_and(And(Or(Not(A), B), C))
    (B & C) | (C & ~A)
    """
    return _distribute((expr, Or, And))


def _distribute(info):
    """
    Distributes info[1] over info[2] with respect to info[0].
    """
    if isinstance(info[0], info[2]):
        for arg in info[0].args:
            if isinstance(arg, info[1]):
                conj = arg
                break
        else:
            return info[0]
        rest = info[2](*[a for a in info[0].args if a is not conj])
        return info[1](*list(map(_distribute,
                                 [(info[2](c, rest), info[1], info[2])
                                  for c in conj.args])))
    elif isinstance(info[0], info[1]):
        return info[1](*list(map(_distribute,
                                 [(x, info[1], info[2])
                                  for x in info[0].args])))
    else:
        return info[0]


def to_nnf(expr, simplify=True):
    """
    Converts expr to Negation Normal Form.
    A logical expression is in Negation Normal Form (NNF) if it
    contains only And, Or and Not, and Not is applied only to literals.
    If simplify is True, the result contains no redundant clauses.

    Examples
    ========

    >>> from sympy.abc import A, B, C, D
    >>> from sympy.logic.boolalg import Not, Equivalent, to_nnf
    >>> to_nnf(Not((~A & ~B) | (C & D)))
    (A | B) & (~C | ~D)
    >>> to_nnf(Equivalent(A >> B, B >> A))
    (A | ~B | (A & ~B)) & (B | ~A | (B & ~A))
    """
    if is_nnf(expr, simplify):
        return expr
    return expr.to_nnf(simplify)


def to_cnf(expr, simplify=False):
    """
    Convert a propositional logical sentence s to conjunctive normal form.
    That is, of the form ((A | ~B | ...) & (B | C | ...) & ...)
    If simplify is True, the expr is evaluated to its simplest CNF form  using
    the Quine-McCluskey algorithm.

    Examples
    ========

    >>> from sympy.logic.boolalg import to_cnf
    >>> from sympy.abc import A, B, D
    >>> to_cnf(~(A | B) | D)
    (D | ~A) & (D | ~B)
    >>> to_cnf((A | B) & (A | ~A), True)
    A | B

    """
    expr = sympify(expr)
    if not isinstance(expr, BooleanFunction):
        return expr

    if simplify:
        return simplify_logic(expr, 'cnf', True)

    # Don't convert unless we have to
    if is_cnf(expr):
        return expr

    expr = eliminate_implications(expr)
    return distribute_and_over_or(expr)


def to_dnf(expr, simplify=False):
    """
    Convert a propositional logical sentence s to disjunctive normal form.
    That is, of the form ((A & ~B & ...) | (B & C & ...) | ...)
    If simplify is True, the expr is evaluated to its simplest DNF form using
    the Quine-McCluskey algorithm.

    Examples
    ========

    >>> from sympy.logic.boolalg import to_dnf
    >>> from sympy.abc import A, B, C
    >>> to_dnf(B & (A | C))
    (A & B) | (B & C)
    >>> to_dnf((A & B) | (A & ~B) | (B & C) | (~B & C), True)
    A | C

    """
    expr = sympify(expr)
    if not isinstance(expr, BooleanFunction):
        return expr

    if simplify:
        return simplify_logic(expr, 'dnf', True)

    # Don't convert unless we have to
    if is_dnf(expr):
        return expr

    expr = eliminate_implications(expr)
    return distribute_or_over_and(expr)


def is_nnf(expr, simplified=True):
    """
    Checks if expr is in Negation Normal Form.
    A logical expression is in Negation Normal Form (NNF) if it
    contains only And, Or and Not, and Not is applied only to literals.
    If simpified is True, checks if result contains no redundant clauses.

    Examples
    ========

    >>> from sympy.abc import A, B, C
    >>> from sympy.logic.boolalg import Not, is_nnf
    >>> is_nnf(A & B | ~C)
    True
    >>> is_nnf((A | ~A) & (B | C))
    False
    >>> is_nnf((A | ~A) & (B | C), False)
    True
    >>> is_nnf(Not(A & B) | C)
    False
    >>> is_nnf((A >> B) & (B >> A))
    False
    """

    expr = sympify(expr)
    if is_literal(expr):
        return True

    stack = [expr]

    while stack:
        expr = stack.pop()
        if expr.func in (And, Or):
            if simplified:
                args = expr.args
                for arg in args:
                    if Not(arg) in args:
                        return False
            stack.extend(expr.args)

        elif not is_literal(expr):
            return False

    return True


def is_cnf(expr):
    """
    Test whether or not an expression is in conjunctive normal form.

    Examples
    ========

    >>> from sympy.logic.boolalg import is_cnf
    >>> from sympy.abc import A, B, C
    >>> is_cnf(A | B | C)
    True
    >>> is_cnf(A & B & C)
    True
    >>> is_cnf((A & B) | C)
    False

    """
    return _is_form(expr, And, Or)


def is_dnf(expr):
    """
    Test whether or not an expression is in disjunctive normal form.

    Examples
    ========

    >>> from sympy.logic.boolalg import is_dnf
    >>> from sympy.abc import A, B, C
    >>> is_dnf(A | B | C)
    True
    >>> is_dnf(A & B & C)
    True
    >>> is_dnf((A & B) | C)
    True
    >>> is_dnf(A & (B | C))
    False

    """
    return _is_form(expr, Or, And)


def _is_form(expr, function1, function2):
    """
    Test whether or not an expression is of the required form.

    """
    expr = sympify(expr)

    # Special case of an Atom
    if expr.is_Atom:
        return True

    # Special case of a single expression of function2
    if isinstance(expr, function2):
        for lit in expr.args:
            if isinstance(lit, Not):
                if not lit.args[0].is_Atom:
                    return False
            else:
                if not lit.is_Atom:
                    return False
        return True

    # Special case of a single negation
    if isinstance(expr, Not):
        if not expr.args[0].is_Atom:
            return False

    if not isinstance(expr, function1):
        return False

    for cls in expr.args:
        if cls.is_Atom:
            continue
        if isinstance(cls, Not):
            if not cls.args[0].is_Atom:
                return False
        elif not isinstance(cls, function2):
            return False
        for lit in cls.args:
            if isinstance(lit, Not):
                if not lit.args[0].is_Atom:
                    return False
            else:
                if not lit.is_Atom:
                    return False

    return True


def eliminate_implications(expr):
    """
    Change >>, <<, and Equivalent into &, |, and ~. That is, return an
    expression that is equivalent to s, but has only &, |, and ~ as logical
    operators.

    Examples
    ========

    >>> from sympy.logic.boolalg import Sufficient, Equivalent, \
         eliminate_implications
    >>> from sympy.abc import A, B, C
    >>> eliminate_implications(Sufficient(A, B))
    B | ~A
    >>> eliminate_implications(Equivalent(A, B))
    (A | ~B) & (B | ~A)
    >>> eliminate_implications(Equivalent(A, B, C))
    (A | ~C) & (B | ~A) & (C | ~B)
    """
    return to_nnf(expr, simplify=False)


def is_literal(expr):
    """
    Returns True if expr is a literal, else False.

    Examples
    ========

    >>> from sympy import Or, Q
    >>> from sympy.abc import A, B
    >>> from sympy.logic.boolalg import is_literal
    >>> is_literal(A)
    True
    >>> is_literal(~A)
    True
    >>> is_literal(Q.zero(A))
    True
    >>> is_literal(A + B)
    True
    >>> is_literal(Or(A, B))
    False
    """
    if isinstance(expr, Not):
        return not isinstance(expr.args[0], BooleanFunction)
    else:
        return not isinstance(expr, BooleanFunction)


def to_int_repr(clauses, symbols):
    """
    Takes clauses in CNF format and puts them into an integer representation.

    Examples
    ========

    >>> from sympy.logic.boolalg import to_int_repr
    >>> from sympy.abc import x, y
    >>> to_int_repr([x | y, y], [x, y]) == [{1, 2}, {2}]
    True

    """

    # Convert the symbol list into a dict
    symbols = dict(list(zip(symbols, list(range(1, len(symbols) + 1)))))

    def append_symbol(arg, symbols):
        if isinstance(arg, Not):
            return -symbols[arg.args[0]]
        else:
            return symbols[arg]

    return [set(append_symbol(arg, symbols) for arg in Or.make_args(c))
            for c in clauses]


def term_to_integer(term):
    """
    Return an integer corresponding to the base-2 digits given by ``term``.

    Parameters
    ==========

    term : a string or list of ones and zeros

    Examples
    ========

    >>> from sympy.logic.boolalg import term_to_integer
    >>> term_to_integer([1, 0, 0])
    4
    >>> term_to_integer('100')
    4

    """

    return int(''.join(list(map(str, list(term)))), 2)


def integer_to_term(k, n_bits=None):
    """
    Return a list of the base-2 digits in the integer, ``k``.

    Parameters
    ==========

    k : int
    n_bits : int
        If ``n_bits`` is given and the number of digits in the binary
        representation of ``k`` is smaller than ``n_bits`` then left-pad the
        list with 0s.

    Examples
    ========

    >>> from sympy.logic.boolalg import integer_to_term
    >>> integer_to_term(4)
    [1, 0, 0]
    >>> integer_to_term(4, 6)
    [0, 0, 0, 1, 0, 0]
    """

    s = '{0:0{1}b}'.format(abs(as_int(k)), as_int(abs(n_bits or 0)))
    return list(map(int, s))


def truth_table(expr, variables, input=True):
    """
    Return a generator of all possible configurations of the input variables,
    and the result of the boolean expression for those values.

    Parameters
    ==========

    expr : string or boolean expression
    variables : list of variables
    input : boolean (default True)
        indicates whether to return the input combinations.

    Examples
    ========

    >>> from sympy.logic.boolalg import truth_table
    >>> from sympy.abc import x,y
    >>> table = truth_table(x >> y, [x, y])
    >>> for t in table:
    ...     print('{0} -> {1}'.format(*t))
    [0, 0] -> True
    [0, 1] -> True
    [1, 0] -> False
    [1, 1] -> True

    >>> table = truth_table(x | y, [x, y])
    >>> list(table)
    [([0, 0], False), ([0, 1], True), ([1, 0], True), ([1, 1], True)]

    If input is false, truth_table returns only a list of truth values.
    In this case, the corresponding input values of variables can be
    deduced from the index of a given output.

    >>> from sympy.logic.boolalg import integer_to_term
    >>> vars = [y, x]
    >>> values = truth_table(x >> y, vars, input=False)
    >>> values = list(values)
    >>> values
    [True, False, True, True]

    >>> for i, value in enumerate(values):
    ...     print('{0} -> {1}'.format(list(zip(
    ...     vars, integer_to_term(i, len(vars)))), value))
    [(y, 0), (x, 0)] -> True
    [(y, 0), (x, 1)] -> False
    [(y, 1), (x, 0)] -> True
    [(y, 1), (x, 1)] -> True

    """
    variables = [sympify(v) for v in variables]

    expr = sympify(expr)
    if not isinstance(expr, BooleanFunction) and not is_literal(expr):
        return

    table = product([0, 1], repeat=len(variables))
    for term in table:
        term = list(term)
        value = expr.xreplace(dict(zip(variables, term)))

        if input:
            yield term, value
        else:
            yield value


def _check_pair(minterm1, minterm2):
    """
    Checks if a pair of minterms differs by only one bit. If yes, returns
    index, else returns -1.
    """
    index = -1
    for x, (i, j) in enumerate(zip(minterm1, minterm2)):
        if i != j:
            if index == -1:
                index = x
            else:
                return -1
    return index


def _convert_to_varsSOP(minterm, variables):
    """
    Converts a term in the expansion of a function from binary to its
    variable form (for SOP).
    """
    temp = []
    for i, m in enumerate(minterm):
        if m == 0:
            temp.append(Not(variables[i]))
        elif m == 1:
            temp.append(variables[i])
        else:
            pass  # ignore the 3s
    return And(*temp)


def _convert_to_varsPOS(maxterm, variables):
    """
    Converts a term in the expansion of a function from binary to its
    variable form (for POS).
    """
    temp = []
    for i, m in enumerate(maxterm):
        if m == 1:
            temp.append(Not(variables[i]))
        elif m == 0:
            temp.append(variables[i])
        else:
            pass  # ignore the 3s
    return Or(*temp)


def _simplified_pairs(terms):
    """
    Reduces a set of minterms, if possible, to a simplified set of minterms
    with one less variable in the terms using QM method.
    """
    simplified_terms = []
    todo = list(range(len(terms)))
    for i, ti in enumerate(terms[:-1]):
        for j_i, tj in enumerate(terms[(i + 1):]):
            index = _check_pair(ti, tj)
            if index != -1:
                todo[i] = todo[j_i + i + 1] = None
                newterm = ti[:]
                newterm[index] = 3
                if newterm not in simplified_terms:
                    simplified_terms.append(newterm)
    simplified_terms.extend(
        [terms[i] for i in [_ for _ in todo if _ is not None]])
    return simplified_terms


def _compare_term(minterm, term):
    """
    Return True if a binary term is satisfied by the given term. Used
    for recognizing prime implicants.
    """
    for i, x in enumerate(term):
        if x != 3 and x != minterm[i]:
            return False
    return True


def _rem_redundancy(l1, terms):
    """
    After the truth table has been sufficiently simplified, use the prime
    implicant table method to recognize and eliminate redundant pairs,
    and return the essential arguments.
    """

    if len(terms):
        # Create dominating matrix
        dommatrix = [[0] * len(l1) for n in range(len(terms))]
        for primei, prime in enumerate(l1):
            for termi, term in enumerate(terms):
                if _compare_term(term, prime):
                    dommatrix[termi][primei] = 1

        # Non-dominated prime implicants, dominated set to None
        ndprimeimplicants = list(range(len(l1)))
        # Non-dominated terms, dominated set to None
        ndterms = list(range(len(terms)))

        # Mark dominated rows and columns
        oldndterms = None
        oldndprimeimplicants = None
        while ndterms != oldndterms or \
                ndprimeimplicants != oldndprimeimplicants:
            oldndterms = ndterms[:]
            oldndprimeimplicants = ndprimeimplicants[:]
            for rowi, row in enumerate(dommatrix):
                if ndterms[rowi] is not None:
                    row = [row[i] for i in
                           [_ for _ in ndprimeimplicants if _ is not None]]
                    for row2i, row2 in enumerate(dommatrix):
                        if rowi != row2i and ndterms[row2i] is not None:
                            row2 = [row2[i] for i in
                                    [_ for _ in ndprimeimplicants
                                     if _ is not None]]
                            if all(a >= b for (a, b) in zip(row2, row)):
                                # row2 dominating row, keep row
                                ndterms[row2i] = None
            for coli in range(len(l1)):
                if ndprimeimplicants[coli] is not None:
                    col = [dommatrix[a][coli] for a in range(len(terms))]
                    col = [col[i] for i in
                           [_ for _ in oldndterms if _ is not None]]
                    for col2i in range(len(l1)):
                        if coli != col2i and \
                                ndprimeimplicants[col2i] is not None:
                            col2 = [dommatrix[a][col2i]
                                    for a in range(len(terms))]
                            col2 = [col2[i] for i in
                                    [_ for _ in oldndterms if _ is not None]]
                            if all(a >= b for (a, b) in zip(col, col2)):
                                # col dominating col2, keep col
                                ndprimeimplicants[col2i] = None
        l1 = [l1[i] for i in [_ for _ in ndprimeimplicants if _ is not None]]

        return l1
    else:
        return []


def _input_to_binlist(inputlist, variables):
    binlist = []
    bits = len(variables)
    for val in inputlist:
        if isinstance(val, int):
            binlist.append(ibin(val, bits))
        elif isinstance(val, dict):
            nonspecvars = list(variables)
            for key in val.keys():
                nonspecvars.remove(key)
            for t in product([0, 1], repeat=len(nonspecvars)):
                d = dict(zip(nonspecvars, t))
                d.update(val)
                binlist.append([d[v] for v in variables])
        elif isinstance(val, (list, tuple)):
            if len(val) != bits:
                raise ValueError("Each term must contain {} bits as there are"
                                 "\n{} variables (or be an integer)."
                                 "".format(bits, bits))
            binlist.append(list(val))
        else:
            raise TypeError("A term list can only contain lists,"
                            " ints or dicts.")
    return binlist


def SOPform(variables, minterms, dontcares=None):
    """
    The SOPform function uses simplified_pairs and a redundant group-
    eliminating algorithm to convert the list of all input combos that
    generate '1' (the minterms) into the smallest Sum of Products form.

    The variables must be given as the first argument.

    Return a logical Or function (i.e., the "sum of products" or "SOP"
    form) that gives the desired outcome. If there are inputs that can
    be ignored, pass them as a list, too.

    The result will be one of the (perhaps many) functions that satisfy
    the conditions.

    Examples
    ========

    >>> from sympy.logic import SOPform
    >>> from sympy import symbols
    >>> w, x, y, z = symbols('w x y z')
    >>> minterms = [[0, 0, 0, 1], [0, 0, 1, 1],
    ...             [0, 1, 1, 1], [1, 0, 1, 1], [1, 1, 1, 1]]
    >>> dontcares = [[0, 0, 0, 0], [0, 0, 1, 0], [0, 1, 0, 1]]
    >>> SOPform([w, x, y, z], minterms, dontcares)
    (y & z) | (z & ~w)

    The terms can also be represented as integers:

    >>> minterms = [1, 3, 7, 11, 15]
    >>> dontcares = [0, 2, 5]
    >>> SOPform([w, x, y, z], minterms, dontcares)
    (y & z) | (z & ~w)

    They can also be specified using dicts, which does not have to be fully
    specified:

    >>> minterms = [{w: 0, x: 1}, {y: 1, z: 1, x: 0}]
    >>> SOPform([w, x, y, z], minterms)
    (x & ~w) | (y & z & ~x)

    Or a combination:

    >>> minterms = [4, 7, 11, [1, 1, 1, 1]]
    >>> dontcares = [{w : 0, x : 0, y: 0}, 5]
    >>> SOPform([w, x, y, z], minterms, dontcares)
    (w & y & z) | (x & y & z) | (~w & ~y)

    References
    ==========

    .. [1] en.wikipedia.org/wiki/Quine-McCluskey_algorithm

    """
    variables = [sympify(v) for v in variables]
    if minterms == []:
        return false

    minterms = _input_to_binlist(minterms, variables)
    dontcares = _input_to_binlist((dontcares or []), variables)
    for d in dontcares:
        if d in minterms:
            raise ValueError('%s in minterms is also in dontcares' % d)

    old = None
    new = minterms + dontcares
    while new != old:
        old = new
        new = _simplified_pairs(old)
    essential = _rem_redundancy(new, minterms)
    return Or(*[_convert_to_varsSOP(x, variables) for x in essential])


def POSform(variables, minterms, dontcares=None):
    """
    The POSform function uses simplified_pairs and a redundant-group
    eliminating algorithm to convert the list of all input combinations
    that generate '1' (the minterms) into the smallest Product of Sums form.

    The variables must be given as the first argument.

    Return a logical And function (i.e., the "product of sums" or "POS"
    form) that gives the desired outcome. If there are inputs that can
    be ignored, pass them as a list, too.

    The result will be one of the (perhaps many) functions that satisfy
    the conditions.

    Examples
    ========

    >>> from sympy.logic import POSform
    >>> from sympy import symbols
    >>> w, x, y, z = symbols('w x y z')
    >>> minterms = [[0, 0, 0, 1], [0, 0, 1, 1], [0, 1, 1, 1],
    ...             [1, 0, 1, 1], [1, 1, 1, 1]]
    >>> dontcares = [[0, 0, 0, 0], [0, 0, 1, 0], [0, 1, 0, 1]]
    >>> POSform([w, x, y, z], minterms, dontcares)
    z & (y | ~w)

    The terms can also be represented as integers:

    >>> minterms = [1, 3, 7, 11, 15]
    >>> dontcares = [0, 2, 5]
    >>> POSform([w, x, y, z], minterms, dontcares)
    z & (y | ~w)

    They can also be specified using dicts, which does not have to be fully
    specified:

    >>> minterms = [{w: 0, x: 1}, {y: 1, z: 1, x: 0}]
    >>> POSform([w, x, y, z], minterms)
    (x | y) & (x | z) & (~w | ~x)

    Or a combination:

    >>> minterms = [4, 7, 11, [1, 1, 1, 1]]
    >>> dontcares = [{w : 0, x : 0, y: 0}, 5]
    >>> POSform([w, x, y, z], minterms, dontcares)
    (w | x) & (y | ~w) & (z | ~y)


    References
    ==========

    .. [1] en.wikipedia.org/wiki/Quine-McCluskey_algorithm

    """
    variables = [sympify(v) for v in variables]
    if minterms == []:
        return false

    minterms = _input_to_binlist(minterms, variables)
    dontcares = _input_to_binlist((dontcares or []), variables)
    for d in dontcares:
        if d in minterms:
            raise ValueError('%s in minterms is also in dontcares' % d)

    maxterms = []
    for t in product([0, 1], repeat=len(variables)):
        t = list(t)
        if (t not in minterms) and (t not in dontcares):
            maxterms.append(t)
    old = None
    new = maxterms + dontcares
    while new != old:
        old = new
        new = _simplified_pairs(old)
    essential = _rem_redundancy(new, maxterms)
    return And(*[_convert_to_varsPOS(x, variables) for x in essential])


def _find_predicates(expr):
    """Helper to find logical predicates in BooleanFunctions.

    A logical predicate is defined here as anything within a BooleanFunction
    that is not a BooleanFunction itself.

    """
    if not isinstance(expr, BooleanFunction):
        return {expr}
    return set().union(*(_find_predicates(i) for i in expr.args))


def simplify_logic(expr, form=None, deep=True, force=False):
    """
    This function simplifies a boolean function to its simplified version
    in SOP or POS form. The return type is an Or or And object in SymPy.

    Parameters
    ==========

    expr : string or boolean expression

    form : string ('cnf' or 'dnf') or None (default).
        If 'cnf' or 'dnf', the simplest expression in the corresponding
        normal form is returned; if None, the answer is returned
        according to the form with fewest args (in CNF by default).

    deep : boolean (default True)
        Indicates whether to recursively simplify any
        non-boolean functions contained within the input.

    force : boolean (default False)
        As the simplifications require exponential time in the number of
        variables, there is by default a limit on expressions with 8 variables.
        When the expression has more than 8 variables only symbolical
        simplification (controlled by ``deep``) is made. By setting force to ``True``, this limit
        is removed. Be aware that this can lead to very long simplification times.

    Examples
    ========

    >>> from sympy.logic import simplify_logic
    >>> from sympy.abc import x, y, z
    >>> from sympy import S
    >>> b = (~x & ~y & ~z) | ( ~x & ~y & z)
    >>> simplify_logic(b)
    ~x & ~y

    >>> S(b)
    (z & ~x & ~y) | (~x & ~y & ~z)
    >>> simplify_logic(_)
    ~x & ~y

    """

    if form not in (None, 'cnf', 'dnf'):
        raise ValueError("form can be cnf or dnf only")
    expr = sympify(expr)
    if deep:
        variables = _find_predicates(expr)
        from sympy.simplify.simplify import simplify
        s = [simplify(v) for v in variables]
        expr = expr.xreplace(dict(zip(variables, s)))
    if not isinstance(expr, BooleanFunction):
        return expr
    # get variables in case not deep or after doing
    # deep simplification since they may have changed
    variables = _find_predicates(expr)
    if not force and len(variables) > 8:
        return expr
    # group into constants and variable values
    c, v = sift(variables, lambda x: x in (True, False), binary=True)
    variables = c + v
    truthtable = []
    # standardize constants to be 1 or 0 in keeping with truthtable
    c = [1 if i == True else 0 for i in c]
    for t in product([0, 1], repeat=len(v)):
        if expr.xreplace(dict(zip(v, t))) == True:
            truthtable.append(c + list(t))
    big = len(truthtable) >= (2 ** (len(variables) - 1))
    if form == 'dnf' or form is None and big:
        return SOPform(variables, truthtable)
    return POSform(variables, truthtable)


def _finger(eq):
    """
    Assign a 5-item fingerprint to each symbol in the equation:
    [
    # of times it appeared as a Symbol,
    # of times it appeared as a Not(symbol),
    # of times it appeared as a Symbol in an And or Or,
    # of times it appeared as a Not(Symbol) in an And or Or,
    sum of the number of arguments with which it appeared
    as a Symbol, counting Symbol as 1 and Not(Symbol) as 2
    and counting self as 1
    ]

    >>> from sympy.logic.boolalg import _finger as finger
    >>> from sympy import And, Or, Not
    >>> from sympy.abc import a, b, x, y
    >>> eq = Or(And(Not(y), a), And(Not(y), b), And(x, y))
    >>> dict(finger(eq))
    {(0, 0, 1, 0, 2): [x], (0, 0, 1, 0, 3): [a, b], (0, 0, 1, 2, 2): [y]}
    >>> dict(finger(x & ~y))
    {(0, 1, 0, 0, 0): [y], (1, 0, 0, 0, 0): [x]}

    The equation must not have more than one level of nesting:

    >>> dict(finger(And(Or(x, y), y)))
    {(0, 0, 1, 0, 2): [x], (1, 0, 1, 0, 2): [y]}
    >>> dict(finger(And(Or(x, And(a, x)), y)))
    Traceback (most recent call last):
    ...
    NotImplementedError: unexpected level of nesting

    So y and x have unique fingerprints, but a and b do not.
    """
    f = eq.free_symbols
    d = dict(list(zip(f, [[0] * 5 for fi in f])))
    for a in eq.args:
        if a.is_Symbol:
            d[a][0] += 1
        elif a.is_Not:
            d[a.args[0]][1] += 1
        else:
            o = len(a.args) + sum(isinstance(ai, Not) for ai in a.args)
            for ai in a.args:
                if ai.is_Symbol:
                    d[ai][2] += 1
                    d[ai][-1] += o
                elif ai.is_Not:
                    d[ai.args[0]][3] += 1
                else:
                    raise NotImplementedError('unexpected level of nesting')
    inv = defaultdict(list)
    for k, v in ordered(iter(d.items())):
        inv[tuple(v)].append(k)
    return inv


def bool_map(bool1, bool2):
    """
    Return the simplified version of bool1, and the mapping of variables
    that makes the two expressions bool1 and bool2 represent the same
    logical behaviour for some correspondence between the variables
    of each.
    If more than one mappings of this sort exist, one of them
    is returned.
    For example, And(x, y) is logically equivalent to And(a, b) for
    the mapping {x: a, y:b} or {x: b, y:a}.
    If no such mapping exists, return False.

    Examples
    ========

    >>> from sympy import SOPform, bool_map, Or, And, Not, Xor
    >>> from sympy.abc import w, x, y, z, a, b, c, d
    >>> function1 = SOPform([x, z, y],[[1, 0, 1], [0, 0, 1]])
    >>> function2 = SOPform([a, b, c],[[1, 0, 1], [1, 0, 0]])
    >>> bool_map(function1, function2)
    (y & ~z, {y: a, z: b})

    The results are not necessarily unique, but they are canonical. Here,
    ``(w, z)`` could be ``(a, d)`` or ``(d, a)``:

    >>> eq =  Or(And(Not(y), w), And(Not(y), z), And(x, y))
    >>> eq2 = Or(And(Not(c), a), And(Not(c), d), And(b, c))
    >>> bool_map(eq, eq2)
    ((x & y) | (w & ~y) | (z & ~y), {w: a, x: b, y: c, z: d})
    >>> eq = And(Xor(a, b), c, And(c,d))
    >>> bool_map(eq, eq.subs(c, x))
    (c & d & (a | b) & (~a | ~b), {a: a, b: b, c: d, d: x})

    """

    def match(function1, function2):
        """Return the mapping that equates variables between two
        simplified boolean expressions if possible.

        By "simplified" we mean that a function has been denested
        and is either an And (or an Or) whose arguments are either
        symbols (x), negated symbols (Not(x)), or Or (or an And) whose
        arguments are only symbols or negated symbols. For example,
        And(x, Not(y), Or(w, Not(z))).

        Basic.match is not robust enough (see issue 4835) so this is
        a workaround that is valid for simplified boolean expressions
        """

        # do some quick checks
        if function1.__class__ != function2.__class__:
            return None  # maybe simplification makes them the same?
        if len(function1.args) != len(function2.args):
            return None  # maybe simplification makes them the same?
        if function1.is_Symbol:
            return {function1: function2}

        # get the fingerprint dictionaries
        f1 = _finger(function1)
        f2 = _finger(function2)

        # more quick checks
        if len(f1) != len(f2):
            return False

        # assemble the match dictionary if possible
        matchdict = {}
        for k in f1.keys():
            if k not in f2:
                return False
            if len(f1[k]) != len(f2[k]):
                return False
            for i, x in enumerate(f1[k]):
                matchdict[x] = f2[k][i]
        return matchdict

    a = simplify_logic(bool1)
    b = simplify_logic(bool2)
    m = match(a, b)
    if m:
        return a, m
    return m


def simplify_patterns_and():
    from sympy.functions.elementary.extremum import Min, Max
    from sympy.core import Wild
    from sympy.core.relational import Eq, Ne, Ge, Gt, Le, Lt
    a = Wild('a')
    b = Wild('b')
    c = Wild('c')
    # With a better canonical fewer results are required
    _matchers_and = ((And(Eq(a, b), Ge(a, b)), Eq(a, b)),
                     (And(Eq(a, b), Gt(a, b)), S.false),
                     (And(Eq(a, b), Le(a, b)), Eq(a, b)),
                     (And(Eq(a, b), Lt(a, b)), S.false),
                     (And(Ge(a, b), Gt(a, b)), Gt(a, b)),
                     (And(Ge(a, b), Le(a, b)), Eq(a, b)),
                     (And(Ge(a, b), Lt(a, b)), S.false),
                     (And(Ge(a, b), Ne(a, b)), Gt(a, b)),
                     (And(Gt(a, b), Le(a, b)), S.false),
                     (And(Gt(a, b), Lt(a, b)), S.false),
                     (And(Gt(a, b), Ne(a, b)), Gt(a, b)),
                     (And(Le(a, b), Lt(a, b)), Lt(a, b)),
                     (And(Le(a, b), Ne(a, b)), Lt(a, b)),
                     (And(Lt(a, b), Ne(a, b)), Lt(a, b)),
                     # Min/max
                     (And(Ge(a, b), Ge(a, c)), Ge(a, Max(b, c))),
                     (And(Ge(a, b), Gt(a, c)), ITE(b > c, Ge(a, b), Gt(a, c))),
                     (And(Gt(a, b), Gt(a, c)), Gt(a, Max(b, c))),
                     (And(Le(a, b), Le(a, c)), Le(a, Min(b, c))),
                     (And(Le(a, b), Lt(a, c)), ITE(b < c, Le(a, b), Lt(a, c))),
                     (And(Lt(a, b), Lt(a, c)), Lt(a, Min(b, c))),
                     # Sign
                     (And(Eq(a, b), Eq(a, -b)), And(Eq(a, S(0)), Eq(b, S(0)))),
                     )
    return _matchers_and


def simplify_patterns_or():
    from sympy.functions.elementary.extremum import Min, Max
    from sympy.core import Wild
    from sympy.core.relational import Eq, Ne, Ge, Gt, Le, Lt
    a = Wild('a')
    b = Wild('b')
    c = Wild('c')
    _matchers_or = ((Or(Eq(a, b), Ge(a, b)), Ge(a, b)),
                    (Or(Eq(a, b), Gt(a, b)), Ge(a, b)),
                    (Or(Eq(a, b), Le(a, b)), Le(a, b)),
                    (Or(Eq(a, b), Lt(a, b)), Le(a, b)),
                    (Or(Ge(a, b), Gt(a, b)), Ge(a, b)),
                    (Or(Ge(a, b), Le(a, b)), S.true),
                    (Or(Ge(a, b), Lt(a, b)), S.true),
                    (Or(Ge(a, b), Ne(a, b)), S.true),
                    (Or(Gt(a, b), Le(a, b)), S.true),
                    (Or(Gt(a, b), Lt(a, b)), Ne(a, b)),
                    (Or(Gt(a, b), Ne(a, b)), Ne(a, b)),
                    (Or(Le(a, b), Lt(a, b)), Le(a, b)),
                    (Or(Le(a, b), Ne(a, b)), S.true),
                    (Or(Lt(a, b), Ne(a, b)), Ne(a, b)),
                    # Min/max
                    (Or(Ge(a, b), Ge(a, c)), Ge(a, Min(b, c))),
                    (Or(Ge(a, b), Gt(a, c)), ITE(b > c, Gt(a, c), Ge(a, b))),
                    (Or(Gt(a, b), Gt(a, c)), Gt(a, Min(b, c))),
                    (Or(Le(a, b), Le(a, c)), Le(a, Max(b, c))),
                    (Or(Le(a, b), Lt(a, c)), ITE(b >= c, Le(a, b), Lt(a, c))),
                    (Or(Lt(a, b), Lt(a, c)), Lt(a, Max(b, c))),
                    )
    return _matchers_or


def simplify_patterns_xor():
    from sympy.functions.elementary.extremum import Min, Max
    from sympy.core import Wild
    from sympy.core.relational import Eq, Ne, Ge, Gt, Le, Lt
    a = Wild('a')
    b = Wild('b')
    c = Wild('c')
    _matchers_xor = ((Xor(Eq(a, b), Ge(a, b)), Gt(a, b)),
                     (Xor(Eq(a, b), Gt(a, b)), Ge(a, b)),
                     (Xor(Eq(a, b), Le(a, b)), Lt(a, b)),
                     (Xor(Eq(a, b), Lt(a, b)), Le(a, b)),
                     (Xor(Ge(a, b), Gt(a, b)), Eq(a, b)),
                     (Xor(Ge(a, b), Le(a, b)), Ne(a, b)),
                     (Xor(Ge(a, b), Lt(a, b)), S.true),
                     (Xor(Ge(a, b), Ne(a, b)), Le(a, b)),
                     (Xor(Gt(a, b), Le(a, b)), S.true),
                     (Xor(Gt(a, b), Lt(a, b)), Ne(a, b)),
                     (Xor(Gt(a, b), Ne(a, b)), Lt(a, b)),
                     (Xor(Le(a, b), Lt(a, b)), Eq(a, b)),
                     (Xor(Le(a, b), Ne(a, b)), Ge(a, b)),
                     (Xor(Lt(a, b), Ne(a, b)), Gt(a, b)),
                     # Min/max
                     (Xor(Ge(a, b), Ge(a, c)),
                      And(Ge(a, Min(b, c)), Lt(a, Max(b, c)))),
                     (Xor(Ge(a, b), Gt(a, c)),
                      ITE(b > c, And(Gt(a, c), Lt(a, b)),
                          And(Ge(a, b), Le(a, c)))),
                     (Xor(Gt(a, b), Gt(a, c)),
                      And(Gt(a, Min(b, c)), Le(a, Max(b, c)))),
                     (Xor(Le(a, b), Le(a, c)),
                      And(Le(a, Max(b, c)), Gt(a, Min(b, c)))),
                     (Xor(Le(a, b), Lt(a, c)),
                      ITE(b < c, And(Lt(a, c), Gt(a, b)),
                          And(Le(a, b), Ge(a, c)))),
                     (Xor(Lt(a, b), Lt(a, c)),
                      And(Lt(a, Max(b, c)), Ge(a, Min(b, c)))),
                     )
    return _matchers_xor
