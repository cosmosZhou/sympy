from sympy.core.basic import Basic
from sympy.core.compatibility import ordered
from sympy.core.evalf import EvalfMixin
from sympy.core.parameters import global_parameters
from sympy.core.relational import Eq, Equal
from sympy.core.singleton import S
from sympy.core.symbol import Symbol
from sympy.core.sympify import sympify
from sympy.logic.boolalg import And, Or
from sympy.sets.contains import Contains
from sympy.utilities import subsets
from sympy.utilities.miscellany import func_name
from sympy.sets.sets import Set, EmptySet, Interval, Complement, Union, is_set, \
    Intersection


class FiniteSet(Set, EvalfMixin):
    """
    Represents a finite set of discrete numbers

    Examples
    ========

    >>> from sympy import FiniteSet
    >>> FiniteSet(1, 2, 3, 4)
    {1, 2, 3, 4}
    >>> 3 in FiniteSet(1, 2, 3, 4)
    True

    >>> members = [1, 2, 3, 4]
    >>> f = FiniteSet(*members)
    >>> f
    {1, 2, 3, 4}
    >>> f - FiniteSet(2)
    {1, 3, 4}
    >>> f + FiniteSet(2, 5)
    {1, 2, 3, 4, 5}

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Finite_set
    """
    is_iterable = True

    def _eval_is_finite(self):
        return True

    def intersection_sets(self, b):
        if b.is_FiniteSet:
            return FiniteSet(*(self._elements & b._elements))

        try:
            return FiniteSet(*[el for el in self if el in b])
        except TypeError:
            return None  # could not evaluate `el in b` due to symbolic ranges.

    def union_sets(self, b):
        if b.is_FiniteSet:
            return FiniteSet(*(set(self.args) | set(b.args)))
        # If `b` set contains one of my elements, remove it from `a`
        if any(b.contains(x) == True for x in self):
            return set((FiniteSet(*[x for x in self if not b.contains(x)]), b))
        
        if b.is_Intersection:
            for i, s in enumerate(b.args):
                if s.is_FiniteSet:
                    u = [*b.args]
                    del u[i]
                    u = b.func(*u, evaluate=False)
                    if self in u:
                        return b.func((self | s), u, evaluate=False)
        if b.is_Complement:
            A, B = b.args
            if B in self:
                return A | self
#         return None

    def __new__(cls, *args, **kwargs):
        evaluate = kwargs.get('evaluate', global_parameters.evaluate)
        if evaluate:
            args = list(map(sympify, args))

            if len(args) == 0:
                return EmptySet()
        else:
            args = list(map(sympify, args))

        args = list(ordered(set(args), Set._infimum_key))
        obj = Basic.__new__(cls, *args)
        return obj

    def _eval_Eq(self, other):
        if not isinstance(other, FiniteSet):
            if other.is_EmptySet:
                return S.false
            
            if other.is_Interval:
                if not other.is_integer:
                    return S.false
                
            if other.is_set:
                return None
            return S.false

        if len(self) != len(other):
            return S.false

    def __iter__(self):
        return iter(self.args)

    def _complement(self, other):
        from sympy import Reals, Integers, Range
        if other.is_Range:
            nums = sorted(m for m in self.args if m.is_number)            
            if False and nums != []:
                syms = [m for m in self.args if m.is_Symbol]
                # Reals cannot contain elements other than numbers and symbols.

                intervals = []  # Build up a list of intervals between the elements
                intervals += [Range(S.NegativeInfinity, nums[0])]
                for a, b in zip(nums[:-1], nums[1:]):
                    intervals.append(Range(a + 1, b))  # both open
                intervals.append(Range(nums[-1] + 1, S.Infinity))

                if syms != []:
                    return Complement(Union(*intervals, evaluate=False), FiniteSet(*syms), evaluate=False)
                else:
                    return Union(*intervals, evaluate=False)
            else:

                for i, e in enumerate(self.args):
                    m, M = other.min(), other.max()
                    if e == M:
                        args = [*self.args]
                        del args[i]
                        return other.copy(stop=M, right_open=True) // self.func(*args)
                    if e == m:
                        args = [*self.args]
                        del args[i]
                        return other.copy(start=m, left_open=True).simplify() // self.func(*args)
                    if e > M or e < m:
                        args = [*self.args]
                        del args[i]
                        return other // self.func(*args)
                return
            
            if other.is_integer:
                if other.min() in self: 
                    return other.copy(start=other.start + 1) // self.func(*{*self.args} - {other.min()})                
                if other.max() in self: 
                    return other.copy(stop=other.stop - 1) // self.func(*{*self.args} - {other.max()})
        elif other.is_Interval:
            nums = sorted(m for m in self.args if m.is_number)
            if other == Reals and nums != []:
                syms = [m for m in self.args if m.is_Symbol]
                # Reals cannot contain elements other than numbers and symbols.

                intervals = []  # Build up a list of intervals between the elements
                intervals += [Interval(S.NegativeInfinity, nums[0], True, True)]
                for a, b in zip(nums[:-1], nums[1:]):
                    intervals.append(Interval(a, b, True, True))  # both open
                intervals.append(Interval(nums[-1], S.Infinity, True, True))

                if syms != []:
                    return Complement(Union(*intervals, evaluate=False),
                            FiniteSet(*syms), evaluate=False)
                else:
                    return Union(*intervals, evaluate=False)
            else:

                for i, e in enumerate(self.args):
                    m, M = other.min(), other.max()
                    if e == M:
                        args = [*self.args]
                        del args[i]
                        return other.copy(stop=M, right_open=True) // self.func(*args)
                    if e == m:
                        args = [*self.args]
                        del args[i]
                        return other.copy(start=m, left_open=True).simplify() // self.func(*args)
                    if e > M or e < m:
                        args = [*self.args]
                        del args[i]
                        return other // self.func(*args)
                return
            
            if other.is_integer:
                if other.min() in self: 
                    return other.copy(start=other.start + 1) // self.func(*{*self.args} - {other.min()})                
                if other.max() in self: 
                    return other.copy(stop=other.stop - 1) // self.func(*{*self.args} - {other.max()})
            
        elif isinstance(other, FiniteSet):
            s = set(self.args)
            _s = set(other.args)
            
            assert s and _s
            intersection = s & _s
#             s -= intersection
            _s -= intersection
            
            unk = []
            
            for i in s:
                if not all(Equal(e, i).is_BooleanFalse for e in _s):
                    unk.append(i)
                    
            if len(unk) == len(s) and not intersection:
                return            
                
            return Complement(FiniteSet(*_s), FiniteSet(*unk))

        return Set._complement(self, other)

    def _contains(self, other):
        """
        Tests whether an element, other, is in the set.

        Relies on Python's set class. This tests for object equality
        All inputs are sympified

        Examples
        ========

        >>> from sympy import FiniteSet
        >>> 1 in FiniteSet(1, 2)
        True
        >>> 5 in FiniteSet(1, 2)
        False

        """
#         r = S.false
        args = []
        for e in self.args:
            # override global evaluation so we can use Eq to do
            # do the evaluation
            t = Eq(e, other, evaluate=True)
            if t is S.true:
                return t
            elif t is not S.false:
                args.append(t)
#                 r = None
        return Or(*args)
#         return r

    @property
    def _boundary(self):
        return self

    @property
    def _inf(self):
        from sympy.functions.elementary.extremum import Min
        return Min(*self)

    @property
    def _sup(self):
        from sympy.functions.elementary.extremum import Max
        return Max(*self)

    @property
    def measure(self):
        return 0

    def __len__(self):
        return len(self.args)

    def as_relational(self, symbol):
        """Rewrite a FiniteSet in terms of equalities and logic operators. """
        return Or(*[Eq(symbol, elem) for elem in self])

    def compare(self, other):
        return (hash(self) - hash(other))

    def _eval_evalf(self, prec):
        return FiniteSet(*[elem._eval_evalf(prec) for elem in self])

    @property
    def _sorted_args(self):
        return self.args

    def _eval_powerset(self):
        return self.func(*[self.func(*s) for s in subsets(self.args)])

    def __ge__(self, other):
        if not other.is_set:
            raise TypeError("Invalid comparison of set with %s" % func_name(other))
        return other.is_subset(self)

    def __gt__(self, other):
        if not other.is_set:
            raise TypeError("Invalid comparison of set with %s" % func_name(other))
        return self.is_proper_superset(other)

    def __le__(self, other):
        if not other.is_set:
            raise TypeError("Invalid comparison of set with %s" % func_name(other))
        return self.is_subset(other)

    def __lt__(self, other):
        if not other.is_set:
            raise TypeError("Invalid comparison of set with %s" % func_name(other))
        return self.is_proper_subset(other)

    def __abs__(self):
        return self._eval_Abs()

    def _eval_Abs(self):
        length = len(self)
        if length == 1:
            return S.One
        from sympy.functions.elementary.piecewise import Piecewise
        * before, last = self.args
        from sympy import Abs       
        before = self.func(*before)
        length = Abs(before)
        return Piecewise((length, Contains(last, before).simplify()), (length + 1, True)).simplify()

    def _eval_is_integer(self):
        for elem in self.args:
            is_integer = elem.is_integer
            if is_integer:
                continue
            return is_integer
        return True

    def _eval_is_extended_real(self): 
        for arg in self.args:
            if arg.is_extended_real:
                continue
            if arg.is_extended_real == False:
                return False
            return 
        return True

    @property
    def etype(self):
        dtype = None
        for e in self:
            _dtype = e.type
            if dtype is None:
                dtype = _dtype
                continue
            if dtype != _dtype:
                if dtype in _dtype:
                    dtype = _dtype
                elif _dtype in dtype:
                    ...
                else:
                    raise Exception('inconsistent dtype detected: %s != %s' % (dtype, _dtype))
        return dtype

    def min(self):
        from sympy.functions.elementary.extremum import Min
        return Min(*self.args)        

    def max(self):
        from sympy.functions.elementary.extremum import Max
        return Max(*self.args)        

    def __add__(self, other):
        if other.is_set:
            return Union(*(other + arg for arg in self.args))
        return self.func(*(arg + other for arg in self.args))

    def __sub__(self, other):
        if is_set(other):
            return Union(*(other - arg for arg in self.args))
        return self.func(*(arg - other for arg in self.args))

    def handle_finite_sets(self, unk):
        if len(unk) == len(self) == 1:
            return Intersection(unk, self, evaluate=False)

    def _eval_domain_defined(self, x, **_):
        domain = Set._eval_domain_defined(self, x)        
        for arg in self.args:
            domain &= arg.domain_defined(x)        
        return domain            

    def sum(self):
        # return the sum of elements in the finiteset
        length = len(self)
        if length == 1:
            return self.arg
        from sympy.functions.elementary.piecewise import Piecewise
        * before, last = self.args
        before = self.func(*before)
        sum_of_before = before.sum()
        return Piecewise((sum_of_before, Contains(last, before).simplify()), (sum_of_before + last, True)).simplify()

    @classmethod
    def simplify_Equal(cls, self, lhs, rhs):
        """
        precondition: self.lhs is a FiniteSet object!
        """
        if rhs.is_FiniteSet:
            if len(lhs) == len(rhs) == 1:
                return self.func(lhs.arg, rhs.arg)
        
    @classmethod
    def simplify_Contains(cls, self, e, s):
        """
        precondition: self.lhs is a FiniteSet object!
        """
        if len(s) == 1:
            y, *_ = s
            if not e._has(Symbol) and y._has(Symbol):
                return Equal(y, e)
            return Equal(e, y)

    @classmethod
    def simplify_NotContains(cls, self, e, s):
        """
        precondition: self.lhs is a FiniteSet object!
        """
        from sympy import Unequal
        if len(s) == 1:
            y, *_ = s
            return Unequal(e, y)
        return And(*(Unequal(e, y) for y in s))

    def _eval_Subset_reversed(self, lhs):
        if lhs.is_UniversalSet:
            return S.false
            

from sympy.core.sympify import converter
converter[set] = lambda x: FiniteSet(*x)
converter[frozenset] = lambda x: FiniteSet(*x)

