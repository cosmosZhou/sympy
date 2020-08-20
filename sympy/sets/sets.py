from __future__ import print_function, division

from itertools import product
import inspect

from sympy.core.basic import Basic
from sympy.core.compatibility import (iterable, with_metaclass,
    ordered, range, PY3)
from sympy.core.cache import cacheit
from sympy.core.evalf import EvalfMixin
from sympy.core.evaluate import global_evaluate
from sympy.core.expr import Expr
from sympy.core.function import Function
from sympy.core.logic import fuzzy_bool
from sympy.core.mul import Mul
from sympy.core.numbers import Float
from sympy.core.operations import LatticeOp
from sympy.core.relational import Eq, Ne, Equality
from sympy.core.singleton import Singleton, S
from sympy.core.symbol import Symbol, Dummy, _uniquely_named_symbol, \
    generate_free_symbol, dtype
from sympy.core.sympify import _sympify, sympify, converter
from sympy.logic.boolalg import And, Or
from sympy.sets.contains import Contains
from sympy.utilities import subsets
from sympy.utilities.iterables import sift
from sympy.utilities.misc import func_name, filldedent

from mpmath import mpi, mpf


class Set(Basic):
    """
    The base class for any kind of set.

    This is not meant to be used directly as a container of items. It does not
    behave like the builtin ``set``; see :class:`FiniteSet` for that.

    Real intervals are represented by the :class:`Interval` class and unions of
    sets by the :class:`Union` class. The empty set is represented by the
    :class:`EmptySet` class and available as a singleton as ``S.EmptySet``.
    """
    is_number = False
    is_set = True
    is_iterable = False
    is_interval = False

    is_FiniteSet = False
    is_ProductSet = False
    is_Union = False
    is_Intersection = None
    is_EmptySet = None

    is_Complement = None
    is_ComplexRegion = False
    
    def _eval_is_finite(self):
        return False
    
    @property
    def domain(self):
        return S.UniversalSet        
    
    @property
    def shape(self):
        return ()
    
    @property
    def list(self):
        return List(self)

    @staticmethod
    def static_assertion(self):
        from sympy.concrete.expr_with_limits import Exists
        e = self.element_symbol()
        return Exists(Contains(e, self), (e,)) | Equality(self, S.EmptySet)
    
    def assertion(self):
        return Set.static_assertion(self)        

    def bisect(self, domain=None, **kwargs):
        if self.is_ExprWithLimits:
            from sympy.concrete.expr_with_limits import ExprWithLimits
            return ExprWithLimits.bisect(self, domain=domain, **kwargs)
        return Union(self & domain, self - domain, evaluate=False)

    def image_set(self):
        return None

    def element_symbol(self, excludes=set()):
        element_type = self.element_type
        return generate_free_symbol(self.free_symbols | excludes, **element_type.dict)

    @property
    def atomic_dtype(self):
        return self.element_type.set

    def could_extract_minus_sign(self):
        return False

    @staticmethod
    def _infimum_key(expr):
        """
        Return infimum (if possible) else S.Infinity.
        """
        try:
            infimum = expr.inf
            assert infimum.is_comparable
        except (NotImplementedError,
                AttributeError, AssertionError, ValueError):
            infimum = S.Infinity
        return infimum

    def union(self, other):
        """
        Returns the union of 'self' and 'other'.

        Examples
        ========

        As a shortcut it is possible to use the '+' operator:

        >>> from sympy import Interval, FiniteSet
        >>> Interval(0, 1).union(Interval(2, 3))
        Union(Interval(0, 1), Interval(2, 3))
        >>> Interval(0, 1) + Interval(2, 3)
        Union(Interval(0, 1), Interval(2, 3))
        >>> Interval(1, 2, True, True) + FiniteSet(2, 3)
        Union(Interval.Lopen(1, 2), {3})

        Similarly it is possible to use the '-' operator for set differences:

        >>> Interval(0, 2) - Interval(0, 1)
        Interval.Lopen(1, 2)
        >>> Interval(1, 3) - FiniteSet(2)
        Union(Interval.Ropen(1, 2), Interval.Lopen(2, 3))

        """
        return Union(self, other)

    def intersect(self, other):
        """
        Returns the intersection of 'self' and 'other'.

        >>> from sympy import Interval

        >>> Interval(1, 3).intersect(Interval(1, 2))
        Interval(1, 2)

        >>> from sympy import imageset, Lambda, symbols, S
        >>> n, m = symbols('n m')
        >>> a = imageset(Lambda(n, 2*n), S.Integers)
        >>> a.intersect(imageset(Lambda(m, 2*m + 1), S.Integers))
        EmptySet()

        """
        return Intersection(self, other)

    def intersection(self, other):
        """
        Alias for :meth:`intersect()`
        """
        return self.intersect(other)

    def is_disjoint(self, other):
        """
        Returns True if 'self' and 'other' are disjoint

        Examples
        ========

        >>> from sympy import Interval
        >>> Interval(0, 2).is_disjoint(Interval(1, 2))
        False
        >>> Interval(0, 2).is_disjoint(Interval(3, 4))
        True

        References
        ==========

        .. [1] https://en.wikipedia.org/wiki/Disjoint_sets
        """
        return self.intersect(other) == S.EmptySet

    def isdisjoint(self, other):
        """
        Alias for :meth:`is_disjoint()`
        """
        return self.is_disjoint(other)

    def complement(self, universe):
        r"""
        The complement of 'self' w.r.t the given universe.

        Examples
        ========

        >>> from sympy import Interval, S
        >>> Interval(0, 1).complement(S.Reals)
        Union(Interval.open(-oo, 0), Interval.open(1, oo))

        >>> Interval(0, 1).complement(S.UniversalSet)
        UniversalSet \ Interval(0, 1)

        """
        return Complement(universe, self)

    def _complement(self, other):
        # this behaves as other - self
        if isinstance(other, ProductSet):
            # For each set consider it or it's complement
            # We need at least one of the sets to be complemented
            # Consider all 2^n combinations.
            # We can conveniently represent these options easily using a
            # ProductSet

            # XXX: this doesn't work if the dimensions of the sets isn't same.
            # A - B is essentially same as A if B has a different
            # dimensionality than A
            switch_sets = ProductSet(FiniteSet(o, o - s) for s, o in
                                     zip(self.sets, other.sets))
            product_sets = (ProductSet(*s) for s in switch_sets)
            # Union of all combinations but this one
            return Union(*(p for p in product_sets if p != other))

        elif isinstance(other, Interval):
            if isinstance(self, Interval) :
                if other.is_integer:
                    return Intersection(other, self.complement(S.Integers))
                return Intersection(other, self.complement(S.Reals))

        elif isinstance(other, Union):
            simplified = []
            unsimplified = []
            hit = False
            for arg in other.args:
                diff = arg - self
                if diff.is_Complement and diff.args[1] == self:
                    hit = diff.args[0] != arg
                    unsimplified.append(diff.args[0])
                else: 
                    hit = True
                    simplified.append(diff)
            if hit:
                simplified = Union(*simplified, evaluate=False) if simplified else S.EmptySet                
                unsimplified = Complement(Union(*unsimplified, evaluate=False), self, evaluate=False) if unsimplified else S.EmptySet
                return simplified | unsimplified

        elif isinstance(other, Complement):
            if other.args[0] in self:
                return S.EmptySet
            return Complement(other.args[0], Union(other.args[1], self), evaluate=False)

        elif isinstance(other, EmptySet):
            return S.EmptySet

        elif isinstance(other, FiniteSet):
            from sympy.utilities.iterables import sift

            sifted = sift(other, lambda x: fuzzy_bool(self.contains(x)))
            # ignore those that are contained in self
            return Union(FiniteSet(*(sifted[False])),
                Complement(FiniteSet(*(sifted[None])), self, evaluate=False)
                if sifted[None] else S.EmptySet)

    def symmetric_difference(self, other):
        """
        Returns symmetric difference of `self` and `other`.

        Examples
        ========

        >>> from sympy import Interval, S
        >>> Interval(1, 3).symmetric_difference(S.Reals)
        Union(Interval.open(-oo, 1), Interval.open(3, oo))
        >>> Interval(1, 10).symmetric_difference(S.Reals)
        Union(Interval.open(-oo, 1), Interval.open(10, oo))

        >>> from sympy import S, EmptySet
        >>> S.Reals.symmetric_difference(EmptySet())
        Reals

        References
        ==========
        .. [1] https://en.wikipedia.org/wiki/Symmetric_difference

        """
        return SymmetricDifference(self, other)

    def _symmetric_difference(self, other):
        return Union(Complement(self, other), Complement(other, self))

    @property
    def inf(self):
        """
        The infimum of 'self'

        Examples
        ========

        >>> from sympy import Interval, Union
        >>> Interval(0, 1).inf
        0
        >>> Union(Interval(0, 1), Interval(2, 3)).inf
        0

        """
        return self._inf

    @property
    def _inf(self):
        raise NotImplementedError("(%s)._inf" % self)

    @property
    def sup(self):
        """
        The supremum of 'self'

        Examples
        ========

        >>> from sympy import Interval, Union
        >>> Interval(0, 1).sup
        1
        >>> Union(Interval(0, 1), Interval(2, 3)).sup
        3

        """
        return self._sup

    @property
    def _sup(self):
        raise NotImplementedError("(%s)._sup" % self)

    def contains(self, other):
        """
        Returns True if 'other' is contained in 'self' as an element.

        As a shortcut it is possible to use the 'in' operator:

        Examples
        ========

        >>> from sympy import Interval
        >>> Interval(0, 1).contains(0.5)
        True
        >>> 0.5 in Interval(0, 1)
        True

        """
        other = sympify(other, strict=True)
        ret = sympify(self._contains(other))
        if ret is not None and ret.is_BooleanAtom:
            return ret
            
        domain_assumed = other.domain_assumed
        if domain_assumed :
            intersect = domain_assumed & self
            if not intersect:
                return S.false
            if intersect == domain_assumed:
                return S.true        
        
        if ret is None:
            ret = Contains(other, self, evaluate=False)
        return ret

    def _contains(self, other):
        raise NotImplementedError("(%s)._contains(%s)" % (self, other))

    def is_subset(self, other):
        """
        Returns True if 'self' is a subset of 'other'.

        Examples
        ========

        >>> from sympy import Interval
        >>> Interval(0, 0.5).is_subset(Interval(0, 1))
        True
        >>> Interval(0, 1).is_subset(Interval(0, 1, left_open=True))
        False

        """
        if other.is_set:
            # XXX issue 16873
            # self might be an unevaluated form of self
            # so the equality test will fail
            return self.intersect(other) == self
        else:
            raise ValueError("Unknown argument '%s'" % other)

    def issubset(self, other):
        """
        Alias for :meth:`is_subset()`
        """
        return self.is_subset(other)

    def is_proper_subset(self, other):
        """
        Returns True if 'self' is a proper subset of 'other'.

        Examples
        ========

        >>> from sympy import Interval
        >>> Interval(0, 0.5).is_proper_subset(Interval(0, 1))
        True
        >>> Interval(0, 1).is_proper_subset(Interval(0, 1))
        False

        """
        if other.is_set:
            return self != other and self.is_subset(other)
        else:
            raise ValueError("Unknown argument '%s'" % other)

    def is_superset(self, other):
        """
        Returns True if 'self' is a superset of 'other'.

        Examples
        ========

        >>> from sympy import Interval
        >>> Interval(0, 0.5).is_superset(Interval(0, 1))
        False
        >>> Interval(0, 1).is_superset(Interval(0, 1, left_open=True))
        True

        """
        if other.is_set:
            return other.is_subset(self)
        else:
            raise ValueError("Unknown argument '%s'" % other)

    def issuperset(self, other):
        """
        Alias for :meth:`is_superset()`
        """
        return self.is_superset(other)

    def is_proper_superset(self, other):
        """
        Returns True if 'self' is a proper superset of 'other'.

        Examples
        ========

        >>> from sympy import Interval
        >>> Interval(0, 1).is_proper_superset(Interval(0, 0.5))
        True
        >>> Interval(0, 1).is_proper_superset(Interval(0, 1))
        False

        """
        if other.is_set:
            return self != other and self.is_superset(other)
        else:
            raise ValueError("Unknown argument '%s'" % other)

    def _eval_powerset(self):
        raise NotImplementedError('Power set not defined for: %s' % self.func)

    def powerset(self):
        """
        Find the Power set of 'self'.

        Examples
        ========

        >>> from sympy import FiniteSet, EmptySet
        >>> A = EmptySet()
        >>> A.powerset()
        {EmptySet()}
        >>> A = FiniteSet(1, 2)
        >>> a, b, c = FiniteSet(1), FiniteSet(2), FiniteSet(1, 2)
        >>> A.powerset() == FiniteSet(a, b, c, EmptySet())
        True

        References
        ==========

        .. [1] https://en.wikipedia.org/wiki/Power_set

        """
        return self._eval_powerset()

    @property
    def measure(self):
        """
        The (Lebesgue) measure of 'self'

        Examples
        ========

        >>> from sympy import Interval, Union
        >>> Interval(0, 1).measure
        1
        >>> Union(Interval(0, 1), Interval(2, 3)).measure
        2

        """
        return self._measure

    @property
    def boundary(self):
        """
        The boundary or frontier of a set

        A point x is on the boundary of a set S if

        1.  x is in the closure of S.
            I.e. Every neighborhood of x contains a point in S.
        2.  x is not in the interior of S.
            I.e. There does not exist an open set centered on x contained
            entirely within S.

        There are the points on the outer rim of S.  If S is open then these
        points need not actually be contained within S.

        For example, the boundary of an interval is its start and end points.
        This is true regardless of whether or not the interval is open.

        Examples
        ========

        >>> from sympy import Interval
        >>> Interval(0, 1).boundary
        {0, 1}
        >>> Interval(0, 1, True, False).boundary
        {0, 1}
        """
        return self._boundary

    @property
    def is_open(self):
        """
        Property method to check whether a set is open.
        A set is open if and only if it has an empty intersection with its
        boundary.

        Examples
        ========
        >>> from sympy import S
        >>> S.Reals.is_open
        True
        """
        if not Intersection(self, self.boundary):
            return True
        # We can't confidently claim that an intersection exists
        return None

    @property
    def is_closed(self):
        """
        A property method to check whether a set is closed. A set is closed
        if it's complement is an open set.

        Examples
        ========
        >>> from sympy import Interval
        >>> Interval(0, 1).is_closed
        True
        """
        return self.boundary.is_subset(self)

    @property
    def closure(self):
        """
        Property method which returns the closure of a set.
        The closure is defined as the union of the set itself and its
        boundary.

        Examples
        ========
        >>> from sympy import S, Interval
        >>> S.Reals.closure
        Reals
        >>> Interval(0, 1).closure
        Interval(0, 1)
        """
        return self + self.boundary

    @property
    def interior(self):
        """
        Property method which returns the interior of a set.
        The interior of a set S consists all points of S that do not
        belong to the boundary of S.

        Examples
        ========
        >>> from sympy import Interval
        >>> Interval(0, 1).interior
        Interval.open(0, 1)
        >>> Interval(0, 1).boundary.interior
        EmptySet()
        """
        return self - self.boundary

    @property
    def _boundary(self):
        raise NotImplementedError()

    @property
    def _measure(self):
        raise NotImplementedError("(%s)._measure" % self)

    def __add__(self, other):
        return self.union(other)

    def __or__(self, other):
        return self.union(other)

    def __and__(self, other):
        return self.intersect(other)

    def __mul__(self, other):
        return ProductSet(self, other)

    def __xor__(self, other):
        return SymmetricDifference(self, other)

    def __pow__(self, exp):
        if not sympify(exp).is_Integer and exp >= 0:
            raise ValueError("%s: Exponent must be a positive Integer" % exp)
        return ProductSet([self] * exp)

    def __sub__(self, other):
        return Complement(self, other)

    # performing other in self
    def __contains__(self, other):
        contains = self.contains_with_subset(other)
        if contains is not None:
            return contains
        
        return sympify(self.contains(other))

    def __abs__(self):
        from sympy.functions.elementary.complexes import Abs
        return Abs(self)

    def conjugate(self):
        from sympy.functions.elementary.complexes import conjugate
        return conjugate(self)

    def _eval_conjugate(self):
        return


class ProductSet(Set):
    """
    Represents a Cartesian Product of Sets.

    Returns a Cartesian product given several sets as either an iterable
    or individual arguments.

    Can use '*' operator on any sets for convenient shorthand.

    Examples
    ========

    >>> from sympy import Interval, FiniteSet, ProductSet
    >>> I = Interval(0, 5); S = FiniteSet(1, 2, 3)
    >>> ProductSet(I, S)
    Interval(0, 5) x {1, 2, 3}

    >>> (2, 2) in ProductSet(I, S)
    True

    >>> Interval(0, 1) * Interval(0, 1) # The unit square
    Interval(0, 1) x Interval(0, 1)

    >>> coin = FiniteSet('H', 'T')
    >>> set(coin**2)
    {(H, H), (H, T), (T, H), (T, T)}


    Notes
    =====

    - Passes most operations down to the argument sets
    - Flattens Products of ProductSets

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Cartesian_product
    """
    is_ProductSet = True

    def intersection_sets(self, b):
        if not b.is_ProductSet:
            return None

        if len(b.args) != len(self.args):
            return S.EmptySet
        return ProductSet(i.intersect(j)
                for i, j in zip(self.sets, b.sets))

    def union_sets(self, b):
        if b.is_ProductSet:
            if b.is_subset(self):
                return self
            if len(b.args) != len(self.args):
                return None
            if self.args[0] == b.args[0]:
                return self.args[0] * Union(ProductSet(self.args[1:]),
                                            ProductSet(b.args[1:]))
            if self.args[-1] == b.args[-1]:
                return Union(ProductSet(self.args[:-1]),
                             ProductSet(b.args[:-1])) * self.args[-1]
            return None
        if b.is_subset(self):
            return self
        return None

    def __new__(cls, *sets, **assumptions):

        def flatten(arg):
            if isinstance(arg, Set) :
                if arg.is_ProductSet:
                    return sum(map(flatten, arg.args), [])
                else:
                    return [arg]
            elif iterable(arg):
                return sum(map(flatten, arg), [])

            if arg.is_set:
                return [arg]

            raise TypeError("Input must be Sets or iterables of Sets")

        sets = flatten(list(sets))

        if EmptySet() in sets or len(sets) == 0:
            return EmptySet()

        if len(sets) == 1:
            return sets[0]

        return Basic.__new__(cls, *sets, **assumptions)

    def _eval_Eq(self, other):
        if not other.is_ProductSet:
            return

        if len(self.args) != len(other.args):
            return S.false

        return And(*(Eq(x, y) for x, y in zip(self.args, other.args)))

    def _contains(self, element):
        """
        'in' operator for ProductSets

        Examples
        ========

        >>> from sympy import Interval
        >>> (2, 3) in Interval(0, 5) * Interval(0, 5)
        True

        >>> (10, 10) in Interval(0, 5) * Interval(0, 5)
        False

        Passes operation on to constituent sets
        """
        try:
            if len(element) != len(self.args):
                return S.false
        except TypeError:  # maybe element isn't an iterable
            return S.false
        return And(*[s.contains(item) for s, item in zip(self.sets, element)])

    @property
    def sets(self):
        return self.args

    @property
    def _boundary(self):
        return Union(*(ProductSet(b + b.boundary if i != j else b.boundary
                                for j, b in enumerate(self.sets))
                                for i, a in enumerate(self.sets)))

    @property
    def is_iterable(self):
        """
        A property method which tests whether a set is iterable or not.
        Returns True if set is iterable, otherwise returns False.

        Examples
        ========

        >>> from sympy import FiniteSet, Interval, ProductSet
        >>> I = Interval(0, 1)
        >>> A = FiniteSet(1, 2, 3, 4, 5)
        >>> I.is_iterable
        False
        >>> A.is_iterable
        True

        """
        return all(s.is_iterable for s in self.sets)

    def __iter__(self):
        """
        A method which implements is_iterable property method.
        If self.is_iterable returns True (both constituent sets are iterable),
        then return the Cartesian Product. Otherwise, raise TypeError.
        """
        if self.is_iterable:
            return product(*self.sets)
        else:
            raise TypeError("Not all constituent sets are iterable")

    @property
    def _measure(self):
        measure = 1
        for s in self.sets:
            measure *= s.measure
        return measure

    def __len__(self):
        return Mul(*[len(s) for s in self.args])

    def __bool__(self):
        return all([bool(s) for s in self.args])

    __nonzero__ = __bool__


class CartesianSpace(Set):
    is_CartesianSpace = True
    
    @property
    def domain(self):
        return S.UniversalSet
    
    @property
    def space(self):
        return self.args[0]

    @property
    def shape(self):
        return ()
    
    @property
    def element_type(self):
        return self.space.element_type * self.space_shape

    @property
    def space_shape(self):
        return self.args[1:]

    @property
    def is_integer(self):
        return self.space.is_integer

    def _contains(self, other):
        if tuple(self.element_type.shape) != tuple(other.shape):
            assert tuple(self.element_type.shape) == tuple(other.shape)
        assert tuple(self.element_type.shape) == tuple(other.shape)        

    def __mul__(self, other):
        if other.is_set:
            assert len(other.element_type.shape) < len(self.element_type.shape)
        return self
    
    def __add__(self, other):
        if other.is_set:
            assert len(other.element_type.shape) < len(self.element_type.shape)
        return self
    
    
class Interval(Set, EvalfMixin):
    """
    Represents a real interval as a Set.

    Usage:
        Returns an interval with end points "start" and "end".

        For left_open=True (default left_open is False) the interval
        will be open on the left. Similarly, for right_open=True the interval
        will be open on the right.

    Examples
    ========

    >>> from sympy import Symbol, Interval
    >>> Interval(0, 1)
    Interval(0, 1)
    >>> Interval.Ropen(0, 1)
    Interval.Ropen(0, 1)
    >>> Interval.Ropen(0, 1)
    Interval.Ropen(0, 1)
    >>> Interval.Lopen(0, 1)
    Interval.Lopen(0, 1)
    >>> Interval.open(0, 1)
    Interval.open(0, 1)

    >>> a = Symbol('a', real=True)
    >>> Interval(0, a)
    Interval(0, a)

    Notes
    =====
    - Only real end points are supported
    - Interval(a, b) with a > b will return the empty set
    - Use the evalf() method to turn an Interval into an mpmath
      'mpi' interval instance

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Interval_%28mathematics%29
    """
    is_Interval = True

    def structure_eq(self, other):
        if not isinstance(other, self.func) or len(self.args) != len(other.args):
            return False
        if self.left_open != other.left_open or self.right_open != other.right_open or self.is_integer != other.is_integer:
            return False
        for x, y in zip(self.args[:2], other.args[:2]):
            if not x.structure_eq(y):
                return False
        return True

    def simplify(self, deep=False):
        if deep:
            hit = False
            args = [*self.args]
            for i, arg in enumerate(self.args[:2]):
                try:
                    _arg = arg.simplify(deep=True)
                except Exception as e:
                    print(type(arg))
                    print(arg)
                    raise e

                if _arg != arg:
                    hit = True
                args[i] = _arg
            if hit:
                return self.func(*args).simplify()
        
        if self.is_integer:
            if self.left_open:
                return self.copy(start=self.start + 1, left_open=False)
        return self

    def intersection_sets(self, b):
        if not b.is_Interval:
            return None
        # handle (-oo, oo)
        infty = S.NegativeInfinity, S.Infinity
        if self == Interval(*infty, integer=self.is_integer):
            l, r = self.left, self.right
            if l.is_real or l in infty or r.is_real or r in infty:
                if self.is_integer and not b.is_integer:
                    return b.copy(integer=True)
                return b

        # We can't intersect [0,3] with [x,6] -- we don't know if x>0 or x<0
        if not self._is_comparable(b):
            from sympy.functions.elementary import miscellaneous

            a_start = self.min()
            b_start = b.min()

            start = miscellaneous.Max(a_start, b_start)

            a_end = self.max()
            b_end = b.max()

#             print("Min(%s, %s) = " % (a_end, b_end), end='')    
            end = miscellaneous.Min(a_end, b_end)
#             print(end)
            return Interval(start, end, integer=self.is_integer or b.is_integer)

        empty = False

        if self.start <= b.end and b.start <= self.end:
            # Get topology right.
            if self.start < b.start:
                start = b.start
                left_open = b.left_open
            elif self.start > b.start:
                start = self.start
                left_open = self.left_open
            else:
                start = self.start
                left_open = self.left_open or b.left_open

            if self.end < b.end:
                end = self.end
                right_open = self.right_open
            elif self.end > b.end:
                end = b.end
                right_open = b.right_open
            else:
                end = self.end
                right_open = self.right_open or b.right_open

            if end - start == 0 and (left_open or right_open):
                empty = True
        else:
            empty = True

        if empty:
            return S.EmptySet

        return Interval(start, end, left_open, right_open, self.is_integer or b.is_integer)

    def _union_sets(self, b, integer=None):
        if self.max() in b:
            from sympy import Min
            return b.copy(start=Min(self.min(), b.min()), integer=integer)
        elif self.min() in b:
            from sympy import Max
            return b.copy(end=Max(self.max(), b.max()), integer=integer)
        elif self in b:
            return b
        elif b in self:
            return self

    def union_sets(self, b):
        if b.is_Interval:
            if self._is_comparable(b):
                from sympy.functions.elementary.miscellaneous import Min, Max
                # Non-overlapping intervals
                end = Min(self.end, b.end)
                start = Max(self.start, b.start)
                if (end < start or
                   (end == start and (end not in self and end not in b))):
                    return None
                else:
                    start = Min(self.start, b.start)
                    end = Max(self.end, b.end)

                    left_open = ((self.start != start or self.left_open) and
                                 (b.start != start or b.left_open))
                    right_open = ((self.end != end or self.right_open) and
                                  (b.end != end or b.right_open))
                    return Interval(start, end, left_open, right_open)
            elif self.is_integer and b.is_integer:
                if self.right_open:
                    if b.left_open:
                        if self.end == b.start:
                            return Interval(self.start, b.end, left_open=self.left_open, right_open=b.right_open, integer=True) - FiniteSet(b.start)
                    else:
                        if self.end == b.start - 1:
                            return Interval(self.start, b.end, left_open=self.left_open, right_open=b.right_open, integer=True) - FiniteSet(self.end)
                        if self.end == b.start:
                            return Interval(self.start, b.end, left_open=self.left_open, right_open=b.right_open, integer=True)
                    
                else:
                    if b.left_open:
                        if self.end == b.start:
                            return Interval(self.start, b.end, left_open=self.left_open, right_open=b.right_open, integer=True)
                        if self.end + 1 == b.start:
                            return Interval(self.start, b.end, left_open=self.left_open, right_open=b.right_open, integer=True) - FiniteSet(b.start)
                    else:
                        if self.end + 1 == b.start - 1:
                            return Interval(self.start, b.end, left_open=self.left_open, right_open=b.right_open, integer=True) - FiniteSet(self.end + 1)
                        if self.end + 1 == b.start:
                            return Interval(self.start, b.end, left_open=self.left_open, right_open=b.right_open, integer=True)

                return self._union_sets(b, integer=True)
            elif not self.is_integer and not b.is_integer:
                return self._union_sets(b, integer=False)
        if b.is_UniversalSet:
            return S.UniversalSet
        if b.is_Complement:
            U, A = b.args             
            if U.is_Interval and not A & self:
                combined = self | U
                if combined.is_Interval:
                    return combined - A 

        # If I have open end points and these endpoints are contained in b
        # But only in case, when endpoints are finite. Because
        # interval does not contain oo or -oo.
        open_left_in_b_and_finite = (self.left_open and
                                         sympify(b.contains(self.start)) is S.true and
                                         self.start.is_finite)
        open_right_in_b_and_finite = (self.right_open and
                                          sympify(b.contains(self.end)) is S.true and
                                          self.end.is_finite)
        if open_left_in_b_and_finite or open_right_in_b_and_finite:
            # Fill in my end points and return
            left_open = self.left_open and self.start not in b
            right_open = self.right_open and self.end not in b            
            new_a = self.copy(left_open=left_open, right_open=right_open)
            return set((new_a, b))
        if self.is_integer:
            drapeau = False
            end = self.end
            right_open = self.right_open
            if right_open:
                if end in b:
                    drapeau = True
                    right_open = False
            else:                
                if end + 1 in b:
                    drapeau = True
                    end += 1                                   

            start = self.start
            left_open = self.left_open
            if left_open:
                if start in b:
                    drapeau = True
                    left_open = False
            else:                
                if start - 1 in b:
                    drapeau = True
                    start -= 1                                    

            if drapeau:
                new_a = Interval(start, end, left_open, right_open, True)
                return set((new_a, b))

    def __new__(cls, start, end, left_open=False, right_open=False, integer=None):

        start = _sympify(start)
        end = _sympify(end)
        left_open = _sympify(left_open)
        right_open = _sympify(right_open)

        if not all(isinstance(self, (type(S.true), type(S.false)))
            for self in [left_open, right_open]):
            raise NotImplementedError(
                "left_open and right_open can have only true/false values, "
                "got %s and %s" % (left_open, right_open))

        inftys = [S.Infinity, S.NegativeInfinity]
        # Only allow real intervals (use symbols with 'is_extended_real=True').
        if not all(i.is_extended_real is not False or i in inftys for i in (start, end)):
            raise ValueError("Non-real intervals are not supported")

        # evaluate if possible
        if end < start:
            return S.EmptySet

        if end == start :
            if left_open or right_open:
                return S.EmptySet
            else:
                if start == S.Infinity or start == S.NegativeInfinity:
                    return S.EmptySet
                return FiniteSet(end)

        # Make sure infinite interval end points are open.
        if start == S.NegativeInfinity:
            left_open = S.true
        if end == S.Infinity:
            right_open = S.true

        infinitesimal = start.is_infinitesimal
        if infinitesimal is True:
            start = start.clear_infinitesimal()
            left_open = S.true

        infinitesimal = end.is_infinitesimal
        if infinitesimal is False:
            end = end.clear_infinitesimal()
            right_open = S.true

        if integer:
            if right_open:
                if left_open:
                    if start == end - 2:
                        return FiniteSet(start + 1)
                else:
                    if start == end - 1:
                        return FiniteSet(start)
                    
                if end.is_Add:
                    try:
                        index = end.args.index(S.One)
                        args = [*end.args]
                        del args[index]
                        end = end.func(*args)
                        right_open = S.false
                    except:
                        ...
                    
            else:
                if left_open:
                    if start == end - 1:
                        return FiniteSet(end)
                else:
                    if start == end:
                        return FiniteSet(end)
                
                if end.is_Add:
                    try:
                        index = end.args.index(S.NegativeOne)
                        args = [*end.args]
                        del args[index]
                        end = end.func(*args)
                        right_open = S.true
                    except:
                        ...
            if not left_open and start.is_Add:
                try:
                    index = start.args.index(S.One)
                    args = [*start.args]
                    del args[index]
                    start = start.func(*args)
                    left_open = S.true
                except:
                    ...
        return Basic.__new__(cls, start, end, left_open, right_open, integer=integer)

    def element_symbol(self, excludes=set()):
        return generate_free_symbol(self.free_symbols | excludes, integer=self.is_integer)

    @property
    def size(self):
        if self.is_integer:
            if self.left_open:
                start = self.start + 1
            else:
                start = self.start
            if self.right_open:
                end = self.end
            else:
                end = self.end + 1
            return end - start
        else:
            return self.end - self.start

    def _eval_Abs(self):
        if self.is_integer:
            return self.size

    @property
    def start(self):
        """
        The left end point of 'self'.

        This property takes the same value as the 'inf' property.

        Examples
        ========

        >>> from sympy import Interval
        >>> Interval(0, 1).start
        0

        """
        return self._args[0]

    _inf = left = start

    @classmethod
    def open(cls, a, b):
        """Return an interval including neither boundary."""
        return cls(a, b, True, True)

    @classmethod
    def Lopen(cls, a, b):
        """Return an interval not including the left boundary."""
        return cls(a, b, True, False)

    @classmethod
    def Ropen(cls, a, b):
        """Return an interval not including the right boundary."""
        return cls(a, b, False, True)

    @property
    def end(self):
        """
        The right end point of 'self'.

        This property takes the same value as the 'sup' property.

        Examples
        ========

        >>> from sympy import Interval
        >>> Interval(0, 1).end
        1

        """
        return self._args[1]

    _sup = right = end

    @property
    def left_open(self):
        """
        True if 'self' is left-open.

        Examples
        ========

        >>> from sympy import Interval
        >>> Interval(0, 1, left_open=True).left_open
        True
        >>> Interval(0, 1, left_open=False).left_open
        False

        """
        return self._args[2]

    @property
    def right_open(self):
        """
        True if 'self' is right-open.

        Examples
        ========

        >>> from sympy import Interval
        >>> Interval(0, 1, right_open=True).right_open
        True
        >>> Interval(0, 1, right_open=False).right_open
        False

        """
        return self._args[3]

    def _complement(self, other):
        if other == S.Reals:
            a = Interval(S.NegativeInfinity, self.start,
                         True, not self.left_open)
            b = Interval(self.end, S.Infinity, not self.right_open, True)
            return Union(a, b, evaluate=False)

        if other == S.Integers:
            a = Interval(S.NegativeInfinity, self.start,
                         True, not self.left_open, integer=True)
            b = Interval(self.end, S.Infinity, not self.right_open, True, integer=True)
            return Union(a, b, evaluate=False)

        if isinstance(other, FiniteSet):
            nums = [m for m in other.args if m.is_number]
            if nums == []:
                return None

        return Set._complement(self, other)

    @property
    def _boundary(self):
        finite_points = [p for p in (self.start, self.end)
                         if abs(p) != S.Infinity]
        return FiniteSet(*finite_points)

    def _contains(self, other):
        if not isinstance(other, Expr) or (
                other is S.Infinity or
                other is S.NegativeInfinity or
                other is S.NaN or
                other is S.ComplexInfinity) or other.is_extended_real is False:
            return S.false

        if self.start is S.NegativeInfinity and self.end is S.Infinity:
            if not other.is_extended_real is None:
                return other.is_extended_real

        if other.is_extended_real is False:
            return S.false
        
        if other.is_extended_real is None:
            return
        
        if self.left_open:
            expr = other > self.start
        else:
            expr = other >= self.start

        if self.right_open:
            expr = And(expr, other < self.end)
        else:
            expr = And(expr, other <= self.end)

        return _sympify(expr)

    @property
    def _measure(self):
        return self.end - self.start

    def to_mpi(self, prec=53):
        return mpi(mpf(self.start._eval_evalf(prec)),
            mpf(self.end._eval_evalf(prec)))

    def _eval_evalf(self, prec):
        return Interval(self.left._eval_evalf(prec),
            self.right._eval_evalf(prec),
                        left_open=self.left_open, right_open=self.right_open)

    def _is_comparable(self, other):
        is_comparable = self.start.is_comparable
        is_comparable &= self.end.is_comparable
        is_comparable &= other.start.is_comparable
        is_comparable &= other.end.is_comparable

        return is_comparable

    @property
    def is_left_unbounded(self):
        """Return ``True`` if the left endpoint is negative infinity. """
        return self.left is S.NegativeInfinity or self.left == Float("-inf")

    @property
    def is_right_unbounded(self):
        """Return ``True`` if the right endpoint is positive infinity. """
        return self.right is S.Infinity or self.right == Float("+inf")

    def as_relational(self, x):
        """Rewrite an interval in terms of inequalities and logic operators."""
        x = sympify(x)
        if self.right_open:
            right = x < self.end
        else:
            right = x <= self.end
        if self.left_open:
            left = self.start < x
        else:
            left = self.start <= x
        return And(left, right)

    def _eval_Eq(self, other):
        if not isinstance(other, Interval):
            if isinstance(other, FiniteSet):
                return S.false
            elif other.is_set:
                return None
            return S.false

        return And(Eq(self.left, other.left),
                   Eq(self.right, other.right),
                   self.left_open == other.left_open,
                   self.right_open == other.right_open)

    @property
    def free_symbols(self):
        return set().union(*[a.free_symbols for a in self.args[:2]])

    def max(self):
        if self.right_open:
            if self.is_integer:
                return self.end - 1
            else:
                from sympy.core.numbers import Infinity
                if isinstance(self.end, Infinity):
                    return self.end
                # negative infinitesimal
                return self.end + S.NegativeInfinitesimal
        return self.end

    def min(self):
        if self.left_open:
            if self.is_integer:
                return self.start + 1
            else:
                from sympy.core.numbers import NegativeInfinity
                if isinstance(self.start, NegativeInfinity):
                    return self.start
                # positive infinitesimal
                return self.start + S.Infinitesimal
        return self.start

    def __add__(self, other):
        if isinstance(other, Expr):
            start = self.start + other
            end = self.end + other
            return self.func(start, end, self.left_open, self.right_open, self.is_integer)

        return Set.__add__(self, other)

    def __mul__(self, other):
        if isinstance(other, Expr):
            start = self.start * other
            end = self.end * other
            is_integer = self.is_integer and other.is_integer
            if other > 0:
                return self.func(start, end, self.left_open, self.right_open, is_integer)
            if other < 0:
                return self.func(end, start, self.right_open, self.left_open, is_integer)
            if other == 0:
                return FiniteSet(0)
            return self.func(S.NegativeInfinity, S.Infinity)

        return Set.__mul__(self, other)

    def cos(self):
        from sympy.core.numbers import epsilon
        start, end, *_ = self.args
        if self.right_open:
            end -= epsilon

        from sympy import cos, floor

        n = floor(start / S.Pi)

        m = floor(end / S.Pi)

        if n.is_even:
            if n == m:
                left_open, right_open, is_integer = self.args[2:]
                return self.func(cos(self.end), cos(start), right_open, left_open, is_integer)
        elif n.is_odd:
            if n == m:
                return self.func(cos(start), cos(self.end), *self.args[2:])

        return self.func(-1, 1)

    def acos(self):
        from sympy import acos

        start, end, *_ = self.args

        return self.func(acos(end), acos(start), self.right_open, self.left_open, self.is_integer)

    def __truediv__(self, other):
        if other > 0:
            return self.func(self.start / other, self.end / other, *self.args[2:])
        if other < 0:
            return self.func(self.end / other, self.start / other, self.right_open, self.left_open, self.is_integer)
        return None

    def _has(self, pattern):
        return self.start._has(pattern) or self.end._has(pattern)

    def copy(self, **kwargs):
        if 'start' not in kwargs:
            kwargs['start'] = self.start

        if 'end' not in kwargs:
            kwargs['end'] = self.end
            
        if 'left_open' not in kwargs:
            kwargs['left_open'] = self.left_open

        if 'right_open' not in kwargs:
            kwargs['right_open'] = self.right_open
            
        if 'integer' not in kwargs:
            kwargs['integer'] = self.is_integer        

        return self.func(**kwargs)

    def _subs(self, old, new, **hints):
        assert old != new
        if self == old:
            return new
        
        hit = False
        args = list(self.args)
        for i, arg in enumerate(args):
            if not hasattr(arg, '_eval_subs'):
                continue
            arg = arg._subs(old, new, **hints)
            if arg != args[i]:
                hit = True
                args[i] = arg
        if hit:
            return self.func(*args, integer=self.is_integer)
        return self

    @property
    def element_type(self):
        if self.is_integer:
            return dtype.integer
        return dtype.real

    def _sympystr(self, _): 
        return '{left_open}{start}{sep} {end}{right_open}'.format(**{'start': self.start, 'end': self.end, 'sep': ';' if self.is_integer else ',',
                             'left_open': '(' if self.left_open else '[',
                             'right_open': ')' if self.right_open else ']'})

    def handle_finite_sets(self, unk):
        if all(arg.domain in self for arg in unk.args):
            return unk

    def _hashable_content(self):
        """Return a tuple of information about self that can be used to
        compute the hash. If a class defines additional attributes,
        like ``name`` in Symbol, then this method should be updated
        accordingly to return such relevant attributes.

        Defining more than _hashable_content is necessary if __eq__ has
        been defined by a class. See note about this in Basic.__eq__."""
        if self.is_integer:
            return (self.min(), self.max(), S.false, S.false, True)
        return self._args

    is_extended_real = True    
    
    def _eval_is_extended_negative(self):
        if self.min().is_extended_nonnegative:
            return False
        if self.max().is_extended_negative:
            return True

    def _eval_is_extended_positive(self):
        if self.max().is_extended_nonpositive:
            return False
        if self.min().is_extended_positive:
            return True

    def _eval_is_zero(self):
        if self.min().is_extended_positive:
            return False
        if self.max().is_extended_negative:
            return False

    def _eval_is_rational(self):
        if self.is_integer:
            return True        

    def _eval_is_algebraic(self):
        if self.is_integer:
            return True        

    def _eval_is_finite(self):
        if self.is_integer:
            if self.start.is_finite:
                return self.end.is_finite
            return self.start.is_finite
        return False

            
class Union(Set, LatticeOp, EvalfMixin):
    """
    Represents a union of sets as a :class:`Set`.

    Examples
    ========

    >>> from sympy import Union, Interval
    >>> Union(Interval(1, 2), Interval(3, 4))
    Union(Interval(1, 2), Interval(3, 4))

    The Union constructor will always try to merge overlapping intervals,
    if possible. For example:

    >>> Union(Interval(1, 2), Interval(2, 3))
    Interval(1, 3)

    See Also
    ========

    Intersection

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Union_%28set_theory%29
    """
    is_Union = True

    @property
    def identity(self):
        return S.EmptySet

    @property
    def zero(self):
        return S.UniversalSet

    def __new__(cls, *args, **kwargs):
        evaluate = kwargs.get('evaluate', global_evaluate[0])

        # flatten inputs to merge intersections and iterables
        args = _sympify(args)
        if len(args) == 1:
            return args[0]
        # Reduce sets using known rules
        if evaluate:
            args = list(cls._new_args_filter(args))
            return simplify_union(args)

        args = list(ordered(args, Set._infimum_key))

        obj = Basic.__new__(cls, *args)
        obj._argset = frozenset(args)
        return obj

    @property
    @cacheit
    def args(self):
        return self._args

    def _complement(self, universe):
        # DeMorgan's Law
        return Intersection(s.complement(universe) for s in self.args)

    @property
    def _inf(self):
        # We use Min so that sup is meaningful in combination with symbolic
        # interval end points.
        from sympy.functions.elementary.miscellaneous import Min
        return Min(*[s.inf for s in self.args])

    @property
    def _sup(self):
        # We use Max so that sup is meaningful in combination with symbolic
        # end points.
        from sympy.functions.elementary.miscellaneous import Max
        return Max(*[s.sup for s in self.args])

    def _contains(self, other):
        return Or(*[s.contains(other) for s in self.args])

    @property
    def _measure(self):
        # Measure of a union is the sum of the measures of the sets minus
        # the sum of their pairwise intersections plus the sum of their
        # triple-wise intersections minus ... etc...

        # Sets is a collection of intersections and a set of elementary
        # sets which made up those intersections (called "sos" for set of sets)
        # An example element might of this list might be:
        #    ( {A,B,C}, A.intersect(B).intersect(C) )

        # Start with just elementary sets (  ({A}, A), ({B}, B), ... )
        # Then get and subtract (  ({A,B}, (A int B), ... ) while non-zero
        sets = [(FiniteSet(s), s) for s in self.args]
        measure = 0
        parity = 1
        while sets:
            # Add up the measure of these sets and add or subtract it to total
            measure += parity * sum(inter.measure for sos, inter in sets)

            # For each intersection in sets, compute the intersection with every
            # other set not already part of the intersection.
            sets = ((sos + FiniteSet(newset), newset.intersect(intersection))
                    for sos, intersection in sets for newset in self.args
                    if newset not in sos)

            # Clear out sets with no measure
            sets = [(sos, inter) for sos, inter in sets if inter.measure != 0]

            # Clear out duplicates
            sos_list = []
            sets_list = []
            for s in sets:
                if s[0] in sos_list:
                    continue
                else:
                    sos_list.append(s[0])
                    sets_list.append(s)
            sets = sets_list

            # Flip Parity - next time subtract/add if we added/subtracted here
            parity *= -1
        return measure

    @property
    def _boundary(self):

        def boundary_of_set(i):
            """ The boundary of set i minus interior of all other sets """
            b = self.args[i].boundary
            for j, a in enumerate(self.args):
                if j != i:
                    b = b - a.interior
            return b

        return Union(*map(boundary_of_set, range(len(self.args))))

    def as_relational(self, symbol):
        """Rewrite a Union in terms of equalities and logic operators. """
        if len(self.args) == 2:
            a, b = self.args
            if (a.sup == b.inf and a.inf is S.NegativeInfinity
                    and b.sup is S.Infinity):
                return And(Ne(symbol, a.sup), symbol < b.sup, symbol > a.inf)
        return Or(*[s.as_relational(symbol) for s in self.args])

    @property
    def is_iterable(self):
        return all(arg.is_iterable for arg in self.args)

    def _eval_evalf(self, prec):
        try:
            return Union(*(s._eval_evalf(prec) for s in self.args))
        except (TypeError, ValueError, NotImplementedError):
            import sys
            raise (TypeError("Not all sets are evalf-able"),
                   None,
                   sys.exc_info()[2])

    def __iter__(self):
        import itertools

        # roundrobin recipe taken from itertools documentation:
        # https://docs.python.org/2/library/itertools.html#recipes
        def roundrobin(*iterables):
            "roundrobin('ABC', 'D', 'EF') --> A D E B F C"
            # Recipe credited to George Sakkis
            pending = len(iterables)
            if PY3:
                nexts = itertools.cycle(iter(it).__next__ for it in iterables)
            else:
                nexts = itertools.cycle(iter(it).next for it in iterables)
            while pending:
                try:
                    for next in nexts:
                        yield next()
                except StopIteration:
                    pending -= 1
                    nexts = itertools.cycle(itertools.islice(nexts, pending))

        if all(s.is_iterable for s in self.args):
            return roundrobin(*(iter(arg) for arg in self.args))
        else:
            raise TypeError("Not all constituent sets are iterable")

    @property
    def is_integer(self):
        for arg in self.args:
            is_integer = arg.is_integer
            if is_integer is True:
                continue
            if is_integer is False:
                return False
            return None
        return True

    @property
    def element_type(self):
        dtype = None
        for e in self.args:
            _dtype = e.element_type
            if dtype is None:
                dtype = _dtype
                continue
            if dtype != _dtype:
                return None

        return dtype

    def rewrite(self, *args, **hints):
        if 'complement' in hints:
            complement = hints['complement']
            A = self.args[complement]
            return self.func(*[(arg if i == complement else A.complement(arg)) for i, arg in enumerate(self.args)], evaluate=False)
        return self

    def _eval_Abs(self):
        non_intersect = []
        args = [*self.args]
        for A in self.args:
            intersect = False
            for B in args:
                if A == B:
                    continue

                if A & B:
                    intersect = True
                    break
            if intersect:
                continue
            non_intersect.append(A)
            args.remove(A)

        from sympy.core.add import Add
        if non_intersect:
            return  Add(*[abs(A) for A in non_intersect]) + abs(self.func(*args))

    def min(self):
        from sympy.functions.elementary.miscellaneous import Min        
        return Min(*(arg.min() for arg in self.args))        

    def max(self):
        from sympy.functions.elementary.miscellaneous import Max        
        return Max(*(arg.max() for arg in self.args))        

    def _sympystr(self, p):
        return ' ∪ '.join(["(%s)" % p._print(a) if a.is_Complement else p._print(a) for a in self.args])

    def _latex(self, p):
        args = []
        for i in self.args:
            latex = p._print(i)
            if i.is_Complement or i.is_Union:
                latex = r'\left(%s\right)' % latex
            args.append(latex)

        return r" \cup ".join(args)

    def _eval_is_finite(self):
        return all(a.is_finite for a in self.args)


class Intersection(Set, LatticeOp):
    """
    Represents an intersection of sets as a :class:`Set`.

    Examples
    ========

    >>> from sympy import Intersection, Interval
    >>> Intersection(Interval(1, 3), Interval(2, 4))
    Interval(2, 3)

    We often use the .intersect method

    >>> Interval(1,3).intersect(Interval(2,4))
    Interval(2, 3)

    See Also
    ========

    Union

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Intersection_%28set_theory%29
    """
    is_Intersection = True

    @property
    def element_type(self):
        dtype = None
        for e in self.args:
            _dtype = e.element_type
            if dtype is None:
                dtype = _dtype
                continue
            if dtype != _dtype:
                return None

        return dtype

    def union_sets(self, b):
# (A - B) | (C & D) = ((A - B) | C) & ((A - B) | D) = (A | C) & ((A - B) | D)
        for c in self.args:
            if c.is_subset(b):
                return b
            
# (A & C) | (B & C) = (A | B) & C           
        if b.is_Intersection:
            C = self._argset & b._argset
            if C:            
                return (self.func(*self._argset - C, evaluate=False) | b.func(*b._argset - C, evaluate=False)) & self.func(*C)             
        
    @property
    def identity(self):
        return S.UniversalSet

    @property
    def zero(self):
        return S.EmptySet

    def __new__(cls, *args, **kwargs):
        evaluate = kwargs.get('evaluate', global_evaluate[0])

        # flatten inputs to merge intersections and iterables
        args = _sympify(args)
        if len(args) == 1:
            return args[0]
        # Reduce sets using known rules
        if evaluate:
            args = list(cls._new_args_filter(args))
            return simplify_intersection(args)

        args = list(ordered(args, Set._infimum_key))

        obj = Basic.__new__(cls, *args)
        obj._argset = frozenset(args)
        return obj

    @property
    @cacheit
    def args(self):
        return self._args

    @property
    def is_iterable(self):
        return any(arg.is_iterable for arg in self.args)

    @property
    def _inf(self):
        raise NotImplementedError()

    @property
    def _sup(self):
        raise NotImplementedError()

    def _contains(self, other):
        return And(*[s.contains(other) for s in self.args])

    def __iter__(self):
        no_iter = True
        for s in self.args:
            if s.is_iterable:
                no_iter = False
                other_sets = set(self.args) - set((s,))
                other = Intersection(*other_sets, evaluate=False)
                for x in s:
                    c = sympify(other.contains(x))
                    if c is S.true:
                        yield x
                    elif c is S.false:
                        pass
                    else:
                        yield c

        if no_iter:
            raise ValueError("None of the constituent sets are iterable")

    @staticmethod
    def _handle_finite_sets(args):
        from sympy.core.logic import fuzzy_and, fuzzy_bool
        from sympy.core.compatibility import zip_longest

        fs_args, other = sift(args, lambda x: x.is_FiniteSet, binary=True)
        if not fs_args:
            return
        fs_args.sort(key=len)
        s = fs_args[0]
        fs_args = fs_args[1:]

        res = []
        unk = []
        for x in s:
            c = fuzzy_and(fuzzy_bool(o.contains(x)) for o in fs_args + other)
            if c:
                res.append(x)
            elif c is None:
                unk.append(x)
            else:
                pass  # drop arg

        res = FiniteSet(*res) if res else S.EmptySet
        if unk:
            symbolic_s_list = [x for x in s if x.has(Symbol)]
            non_symbolic_s = s - FiniteSet(*symbolic_s_list)
            while fs_args:
                v = fs_args.pop()
                if all(i == j for i, j in zip_longest(symbolic_s_list, (x for x in v if x.has(Symbol)))):
                    # all the symbolic elements of `v` are the same
                    # as in `s` so remove the non-symbol containing
                    # expressions from `unk`, since they cannot be
                    # contained
                    if non_symbolic_s.is_FiniteSet:
                        for x in non_symbolic_s:
                            if x in unk:
                                unk.remove(x)
                else:
                    # if only a subset of elements in `s` are
                    # contained in `v` then remove them from `v`
                    # and add this as a new arg
                    contained = [x for x in symbolic_s_list if sympify(v.contains(x)) is S.true]
                    if contained != symbolic_s_list:
                        other.append(v - FiniteSet(*contained))
                    else:
                        other.append(v)
#                         pass  # for coverage

            other_sets = Intersection(*other)
            if not other_sets:
                return S.EmptySet  # b/c we use evaluate=False below
            elif other_sets == S.UniversalSet:
                res |= FiniteSet(*unk)
            else:
                unk = FiniteSet(*unk)
                result = other_sets.handle_finite_sets(unk)
                if result is not None:
                    return res | result
                return res | Intersection(unk, other_sets, evaluate=False) 
        return res

    def as_relational(self, symbol):
        """Rewrite an Intersection in terms of equalities and logic operators"""
        return And(*[s.as_relational(symbol) for s in self.args])

    def distribute(self):
        for i, union in enumerate(self.args):
            if union.is_UnionComprehension:
                args = [*self.args]
                del args[i]
                this = self.func(*args)
                function = union.function & this
                return union.func(function, *union.limits).simplify()
        return self

    """
    precondition: this set should not be empty!
    """

    def min(self):
        from sympy.functions.elementary.miscellaneous import Max        
        return Max(*(arg.min() for arg in self.args))        

    """
    precondition: this set should not be empty!
    """

    def max(self):
        from sympy.functions.elementary.miscellaneous import Min        
        return Min(*(arg.max() for arg in self.args))

    def _sympystr(self, p):
        return ' ∩ '.join(["(%s)" % p._print(a) if a.is_Complement else p._print(a) for a in self.args])

    def _latex(self, p):
        args = []
        for i in self.args:
            latex = p._print(i)
            if i.is_Complement or i.is_Union:
                latex = r'\left(%s\right)' % latex
            args.append(latex)

        return r" \cap ".join(args)

    def handle_finite_sets(self, unk):
        if len(unk) == 1:
            e, *_ = unk.args
            for i, s in enumerate(self.args):
                if e in s:
                    args = [*self.args]
                    args[i] = unk
                    return self.func(*args, evaluate=False)
                
    def _eval_is_finite(self):
        return any(a.is_finite for a in self.args)
            
            
class Complement(Set, EvalfMixin):
    r"""Represents the set difference or relative complement of a set with
    another set.

    `A - B = \{x \in A| x \\notin B\}`


    Examples
    ========

    >>> from sympy import Complement, FiniteSet
    >>> Complement(FiniteSet(0, 1, 2), FiniteSet(1))
    {0, 2}

    See Also
    =========

    Intersection, Union

    References
    ==========

    .. [1] http://mathworld.wolfram.com/ComplementSet.html
    """

    is_Complement = True

    def _latex(self, p):
        A, B = self.args
        if B.is_Complement:
            B = r"\left(%s\right)" % p._print(B)
        else:
            B = p._print(B)
            
        return r"%s \setminus %s" % (p._print(A), B)

    def _sympystr(self, p): 
        A, B = self.args
        if B.is_Complement:
            B = r"(%s)" % p._print(B)
        else:
            B = p._print(B)
            
        return r"%s \ %s" % (p._print(A), B)

    def assertion(self):
        A, B = self.args
        return Equality(abs(Union(A, B)), abs(self) + abs(B))
    
    def is_connected_interval(self):        
        A, B = self.args
        
        if not A.is_Interval:
            return False
        
        if B.is_Interval:
            return True
            
        if not B.is_FiniteSet:
            return False
        
        if len(B) == 1:
            return True
        
        if not A.is_integer:
            return False
        
        return B.is_integer and B.max() - B.min() == len(B) - 1
        
    def min(self):        
        from sympy.core.numbers import epsilon
        from sympy import floor
        from sympy.functions.elementary.piecewise import Piecewise
        from sympy.concrete.expr_with_limits import Minimum        
        if not self.is_connected_interval():
            return Minimum(self)
                    
        A, B = self.args
        x = A.min()
        
        M = B.max()        
        if A.is_integer:            
            M = floor(M) + 1
        else:
            M += epsilon
            
        return Piecewise((M, Contains(x, B).simplify()), (x, True)).simplify()

    def max(self):
        from sympy.core.numbers import epsilon
        from sympy import ceiling
        from sympy.functions.elementary.piecewise import Piecewise
        from sympy.concrete.expr_with_limits import Maximum        
        if not self.is_connected_interval():
            return Maximum(self)
                    
        A, B = self.args
        x = A.max()
        
        m = B.min()        
        if A.is_integer:                         
            m = ceiling(m) - 1
        else:
            m -= epsilon
            
        return Piecewise((m, Contains(x, B).simplify()), (x, True)).simplify()  

    @property
    def element_type(self):
        return self.args[0].element_type

    def __new__(cls, a, b, evaluate=True):
        if isinstance(b, set):
            b = FiniteSet(*b)

        if isinstance(a, set):
            a = FiniteSet(*a)

        if evaluate:
            return Complement.reduce(a, b)

        return Basic.__new__(cls, a, b)

# A - (B - (A & B)) = A
# A  &  (B - (A & B)) = 0
# (A & B)  &  (B - (A & B)) = 0
# A - (B - A & b), b in B
    def _complement(self, A):
        B, C = self.args
        if C.is_Intersection:
            args = [*C.args]
            try:
                index = args.index(A)
                del args[index]
                b = C.func(*args, evaluate=False)
                if b == B:
                    return A
                if b in B:
                    B -= b
                    return self.func(A, B, evaluate=False)
            except:
                return
        if A in B | C:
            return A & C
        if not A & C:
            return A - B
        if B in A:
#             if C in B:
#                 return (A - B) | C
            if C in A:  # C in B => C in A
                return (A - B) | C
#             return (A - B) | (B & C)

    @staticmethod
    def reduce(A, B):
        """
        Simplify a :class:`Complement`.

        """
        if B == S.UniversalSet or A.is_subset(B):
            return EmptySet()

        if B.is_Union:
            return Intersection(*(s.complement(A) for s in B.args))

        result = B._complement(A)
        if result is not None:
            return result

        if A.is_Union:
            for i, arg in enumerate(A.args):
                if arg in B:
                    args = [*A.args]
                    del args[i]
                    A = A.func(*args)
                    return A - B
                 
        if A.is_UnionComprehension:
            if A.is_ConditionSet:
                if not B.is_ConditionSet:
                    from sympy.sets.conditionset import conditionset
                    base_set = B._complement(A.base_set)
                    if base_set is not None:
                        if A.base_set == base_set:
                            return A
                        return conditionset(A.variable, A.condition, base_set)
            else:
                from sympy import Wild
                for i, domain in A.limits_dict.items():
                    i_ = Wild(i.name)
    
                    dic = B.match(A.function.subs(i, i_))
                    if dic:
                        i_match = dic[i_]
                        if i_match not in domain:
                            return A
        if B.is_Intersection and A in B._argset:
            B = B.func(*B._argset - {A}, evaluate=False)
            
        if A.is_Piecewise:
            return A.func(*((e - B, c) for e, c in A.args)).simplify()
        
        if A.is_Intersection:
            for i, arg in enumerate(A.args):
                if arg.is_Complement and arg.args[1] in B: 
                    args = [*A.args]
                    args[i] = arg.args[0]
                    A = A.func(*args, evaluate=False)
                    return A - B
                     
        if A.is_Complement:
            _, _B = A.args
            if B in _B:
                return A
        return Complement(A, B, evaluate=False)

    def _contains(self, other):
        A = self.args[0]
        B = self.args[1]
        return And(A.contains(other), B.contains(other).invert())

    def union_sets(self, C):
        A, B = self.args
        if B in C:
            return A | C
        if A in C:
            return C
        if C.is_Intersection:
            if A & B in C:
                return A | C
            try:
                # A & B | (A-B) = A
                # A & B | (A-(B+C)) = A - C
                args = [*C.args]
                index = args.index(A)
                del args[index]
                rest = C.func(*args, evaluate=False)
                if rest in B:
                    return A - (B - rest)
            except:
                return
        if C in B:
            B -= C
            return self.func(A, B, evaluate=False)
        if C.is_Complement:
            _A, _B = C.args
            if B == _B:
                return (A | _A) - B
            if _B in self:
                return _A | self

# if B => C, (A - B) | C = A | C
# if A => C, (A - B) | C = C

    def _eval_is_integer(self):
        return self.args[0].is_integer

    def _eval_is_extended_real(self):
        return self.args[0].is_extended_real
    
    def _eval_is_extended_negative(self):
        return self.args[0].is_extended_negative

    def _eval_is_extended_positive(self):
        return self.args[0].is_extended_positive

    def _eval_is_zero(self):
        return self.args[0].is_zero

    def _eval_is_rational(self):
        return self.args[0].is_rational

    def _eval_is_finite(self):
        return self.args[0].is_finite

    def _eval_is_complex(self):
        return self.args[0].is_complex

    def domain_defined(self, x):
        A, B = self.args
        return A.domain_defined(x) & B.domain_defined(x)

    def supremum(self):
        return self.args[0].max()

    def infimum(self):
        return self.args[0].min()
    
    def handle_finite_sets(self, unk):
        A, B = self.args
        if unk in B:
            return S.EmptySet
        if unk in A:
            if B.is_Intersection:
                args = []
                for s in B.args:
                    if unk in s:
                        continue
                    args.append(s)
                if len(args) != len(B.args):
                    B = B.func(*args)
                        
            return self.func(unk, B, evaluate=False)
            
class EmptySet(with_metaclass(Singleton, Set)):
    """
    Represents the empty set. The empty set is available as a singleton
    as S.EmptySet.

    Examples
    ========

    >>> from sympy import S, Interval
    >>> S.EmptySet
    EmptySet()

    >>> Interval(1, 2).intersect(S.EmptySet)
    EmptySet()

    See Also
    ========

    UniversalSet

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Empty_set
    """
    is_EmptySet = True
    is_FiniteSet = True

    def _eval_is_finite(self):
        return True

    @property
    def atomic_dtype(self):
        return None

    def _eval_Abs(self):
        return 0

    def intersection_sets(self, b):
        return self

    def union_sets(self, b):
        return b

    @property
    def _measure(self):
        return 0

    def _contains(self, other):
        return S.false

    def as_relational(self, symbol):
        return S.false

    def __len__(self):
        return 0

    def __iter__(self):
        return iter([])

    def _eval_powerset(self):
        return FiniteSet(self)

    @property
    def _boundary(self):
        return self

    def _complement(self, other):
        return other

    def _symmetric_difference(self, other):
        return other

    def _sympystr(self, _):
        return 'Ø'


class UniversalSet(with_metaclass(Singleton, Set)):
    """
    Represents the set of all things.
    The universal set is available as a singleton as S.UniversalSet

    Examples
    ========

    >>> from sympy import S, Interval
    >>> S.UniversalSet
    UniversalSet

    >>> Interval(1, 2).intersect(S.UniversalSet)
    Interval(1, 2)

    See Also
    ========

    EmptySet

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Universal_set
    """

    is_UniversalSet = True

    def intersection_sets(self, b):
        return b

    def union_sets(self, b):
        return self

    def _complement(self, other):
        return S.EmptySet

    def _symmetric_difference(self, other):
        return other

    @property
    def _measure(self):
        return S.Infinity

    def _contains(self, other):
        return S.true

    def as_relational(self, symbol):
        return S.true

    @property
    def _boundary(self):
        return EmptySet()


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
    is_FiniteSet = True
    is_iterable = True

    def _eval_is_finite(self):
        return True

#     def _subs(self, old, new, **hints):
#         return Set._subs(self, old, new, **hints)

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
        evaluate = kwargs.get('evaluate', global_evaluate[0])
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
            if isinstance(other, (Interval, EmptySet)):
                return S.false
            elif other.is_set:
                return None
            return S.false

        if len(self) != len(other):
            return S.false
        return None
#         return And(*(Eq(x, y) for x, y in zip(self.args, other.args)))

    def __iter__(self):
        return iter(self.args)

    def _complement(self, other):
        if isinstance(other, Interval):
            nums = sorted(m for m in self.args if m.is_number)
            if other == S.Reals and nums != []:
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
#             elif not nums:
                for i, e in enumerate(self.args):
                    if not other.right_open and e == other.end:
                        args = [*self.args]
                        del args[i]
                        return other.copy(right_open=True) - self.func(*args)
                    if not other.left_open and e == other.start:
                        args = [*self.args]
                        del args[i]
                        return other.copy(left_open=True).simplify() - self.func(*args)
                    if e > other.max() or e < other.min():
                        args = [*self.args]
                        del args[i]
                        return other - self.func(*args)
                return
            
            if other.is_integer:
                if other.min() in self:               
                    return other.copy(start=other.start + 1) - self.func(*{*self.args} - {other.min()})                
                if other.max() in self:                
                    return other.copy(end=other.end - 1) - self.func(*{*self.args} - {other.max()})
            
        elif isinstance(other, FiniteSet):
            s = set(self.args)
            _s = set(other.args)
            
            assert s and _s
            intersection = s & _s
#             s -= intersection
            _s -= intersection
            
            unk = []
            
            for i in s:
                if not all(Equality(e, i).is_BooleanFalse for e in _s):
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
        from sympy.functions.elementary.miscellaneous import Min
        return Min(*self)

    @property
    def _sup(self):
        from sympy.functions.elementary.miscellaneous import Max
        return Max(*self)

    @property
    def measure(self):
        return 0

    def __len__(self):
        return len(self.args)

    def as_relational(self, symbol):
        """Rewrite a FiniteSet in terms of equalities and logic operators. """
        from sympy.core.relational import Eq
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
        return len(self)

    def _eval_Abs(self):
        return len(self)

    @property
    def is_integer(self):
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
            if arg.is_extended_real is False:
                return False
            return 
        return True

    @property
    def element_type(self):
        dtype = None
        for e in self:
            _dtype = e.dtype
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
        from sympy.functions.elementary.miscellaneous import Min
        return Min(*self.args)        

    def max(self):
        from sympy.functions.elementary.miscellaneous import Max
        return Max(*self.args)        

    def handle_finite_sets(self, unk):
        if len(unk) == len(self) == 1:
            return Intersection(unk, self, evaluate=False)
#             from sympy import Piecewise
#             return Piecewise((unk, Equality(unk.arg, self.arg)), (S.EmptySet, True)).simplify()


class FiniteList(Expr):
    """
    Represents a finite list of discrete numbers

    Examples
    ========

    >>> from sympy import FiniteSet
    >>> FiniteList(1, 2, 3, 4)
    [1, 2, 3, 4]
    >>> members = [1, 2, 3, 4]
    >>> f = FiniteList(*members)
    >>> f
    [1, 2, 3, 4]
    """
    is_FiniteList = True
    is_iterable = True

    def __new__(cls, *args):
        args = list(map(sympify, args))
        obj = Basic.__new__(cls, *args)
        return obj

    def __iter__(self):
        return iter(self.args)

    def __len__(self):
        return len(self.args)

    @property
    def is_integer(self):
        for elem in self:
            is_integer = elem.is_integer
            if is_integer:
                continue
            return is_integer
        return True

    @property
    def atomic_dtype(self):
        dtype = None
        for e in self.args:
            _dtype = e.dtype
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
        return dtype.set


converter[set] = lambda x: FiniteSet(*x)
converter[frozenset] = lambda x: FiniteSet(*x)


class SymmetricDifference(Set):
    """Represents the set of elements which are in either of the
    sets and not in their intersection.

    Examples
    ========

    >>> from sympy import SymmetricDifference, FiniteSet
    >>> SymmetricDifference(FiniteSet(1, 2, 3), FiniteSet(3, 4, 5))
    {1, 2, 4, 5}

    See Also
    ========

    Complement, Union

    References
    ==========

    .. [1] https://en.wikipedia.org/wiki/Symmetric_difference
    """

    is_SymmetricDifference = True

    def __new__(cls, a, b, evaluate=True):
        if evaluate:
            return SymmetricDifference.reduce(a, b)

        return Basic.__new__(cls, a, b)

    @staticmethod
    def reduce(A, B):
        result = B._symmetric_difference(A)
        if result is not None:
            return result
        else:
            return SymmetricDifference(A, B, evaluate=False)


# image_set is to be substituted for imageset
def image_set(sym, expr, condition):
    from sympy.concrete.expr_with_limits import UnionComprehension
    if condition.is_Interval and condition.is_integer:
        limit = (sym, condition.min(), condition.max())
    else:
        limit = (sym, condition)
    return UnionComprehension({expr}, limit)


def imageset(*args):
    r"""
    Return an image of the set under transformation ``f``.

    If this function can't compute the image, it returns an
    unevaluated ImageSet object.

    .. math::
        { f(x) | x \in self }

    Examples
    ========

    >>> from sympy import S, Interval, Symbol, imageset, sin, Lambda
    >>> from sympy.abc import x, y

    >>> imageset(x, 2*x, Interval(0, 2))
    Interval(0, 4)

    >>> imageset(lambda x: 2*x, Interval(0, 2))
    Interval(0, 4)

    >>> imageset(Lambda(x, sin(x)), Interval(-2, 1))
    ImageSet(Lambda(x, sin(x)), Interval(-2, 1))

    >>> imageset(sin, Interval(-2, 1))
    ImageSet(Lambda(x, sin(x)), Interval(-2, 1))
    >>> imageset(lambda y: x + y, Interval(-2, 1))
    ImageSet(Lambda(y, x + y), Interval(-2, 1))

    Expressions applied to the set of Integers are simplified
    to show as few negatives as possible and linear expressions
    are converted to a canonical form. If this is not desirable
    then the unevaluated ImageSet should be used.

    >>> imageset(x, -2*x + 5, S.Integers)
    ImageSet(Lambda(x, 2*x + 1), Integers)

    See Also
    ========

    sympy.sets.fancysets.ImageSet

    """
    from sympy.core import Lambda
    from sympy.sets.fancysets import ImageSet
    from sympy.sets.setexpr import set_function

    if len(args) < 2:
        raise ValueError('imageset expects at least 2 args, got: %s' % len(args))

    from sympy.tensor.indexed import Slice
    if isinstance(args[0], (Symbol, tuple, Slice)) and len(args) > 2:
        f = Lambda(args[0], args[1])
        set_list = args[2:]
    else:
        f = args[0]
        set_list = args[1:]

    if isinstance(f, Lambda):
        pass
    elif callable(f):
        nargs = getattr(f, 'nargs', {})
        if nargs:
            if len(nargs) != 1:
                raise NotImplemented(filldedent('''
                    This function can take more than 1 arg
                    but the potentially complicated set input
                    has not been analyzed at this point to
                    know its dimensions. TODO
                    '''))
            N = nargs.args[0]
            if N == 1:
                s = 'x'
            else:
                s = [Symbol('x%i' % i) for i in range(1, N + 1)]
        else:
            if PY3:
                s = inspect.signature(f).parameters
            else:
                s = inspect.getargspec(f).args
        dexpr = _sympify(f(*[Dummy() for i in s]))
        var = [_uniquely_named_symbol(Symbol(i), dexpr) for i in s]
        expr = f(*var)
        f = Lambda(var, expr)
    else:
        raise TypeError(filldedent('''
            expecting lambda, Lambda, or FunctionClass,
            not \'%s\'.''' % func_name(f)))

    if any(not s.is_set for s in set_list):
        name = [func_name(s) for s in set_list]
        raise ValueError('arguments after mapping should be sets, not %s' % name)

    if len(set_list) == 1:
        set = set_list[0]
        try:
            # TypeError if arg count != set dimensions
            r = set_function(f, set)
            if r is None:
                raise TypeError
            if not r:
                return r
        except TypeError:
            r = ImageSet(f, set)
        if isinstance(r, ImageSet):
            f, set = r.args

        if f.variables == f.expr:
            return set

        if isinstance(set, ImageSet):
            if len(set.lamda.variables) == 1 and len(f.variables) == 1:
                return imageset(Lambda(set.lamda.variables[0],
                                       f.expr.subs(f.variables[0], set.lamda.expr)),
                                set.base_set)

        if r is not None:
            return r

    return ImageSet(f, *set_list)


def is_function_invertible_in_set(func, setv):
    """
    Checks whether function ``func`` is invertible when the domain is
    restricted to set ``setv``.
    """
    from sympy import exp, log
    # Functions known to always be invertible:
    if func in (exp, log):
        return True
    u = Dummy("u")
    fdiff = func(u).diff(u)
    # monotonous functions:
    # TODO: check subsets (`func` in `setv`)
    if (fdiff > 0) == True or (fdiff < 0) == True:
        return True
    # TODO: support more
    return None


def simplify_union(args):
    """
    Simplify a :class:`Union` using known rules

    We first start with global rules like 'Merge all FiniteSets'

    Then we iterate through all pairs and ask the constituent sets if they
    can simplify themselves with any other constituent.  This process depends
    on ``union_sets(a, b)`` functions.
    """
#     from sympy.sets.handlers.union import union_sets

    # ===== Global Rules =====
    if not args:
        return S.EmptySet

    for arg in args:
        if not arg.is_set:
            raise TypeError("Input args to Union must be Sets")

    # Merge all finite sets
    finite_sets = [x for x in args if x.is_FiniteSet]
    if len(finite_sets) > 1:
        a = (x for s in finite_sets for x in s)
        finite_set = FiniteSet(*a)
        args = [finite_set] + [x for x in args if not x.is_FiniteSet]

    # ===== Pair-wise Rules =====
    # Here we depend on rules built into the constituent sets
    args = set(args)
    new_args = True
    while new_args:
        for s in args:
            new_args = False
            for t in args - set((s,)):
                new_set = s.union_sets(t)
                # This returns None if s does not know how to intersect
                # with t. Returns the newly intersected set otherwise
                if new_set is not None:
                    if not isinstance(new_set, set):
                        new_set = set((new_set,))
                    new_args = (args - set((s, t))).union(new_set)
                    break
            if new_args:
                args = new_args
                break

    if len(args) == 1:
        return args.pop()
    else:
        return Union(*args, evaluate=False)


def simplify_intersection(args):
    """
    Simplify an intersection using known rules

    We first start with global rules like
    'if any empty sets return empty set' and 'distribute any unions'

    Then we iterate through all pairs and ask the constituent sets if they
    can simplify themselves with any other constituent
    """

    # ===== Global Rules =====
    if not args:
        return S.UniversalSet

    for arg in args:
        if not arg.is_set:
            raise TypeError("Input args to Union must be Sets")

    # If any EmptySets return EmptySet
    if any(s.is_EmptySet for s in args):
        return S.EmptySet

    # Handle Finite sets
    rv = Intersection._handle_finite_sets(args)

    if rv is not None:
        return rv

    # If any of the sets are unions, return a Union of Intersections
    for s in args:
        if s.is_Union:
            other_sets = set(args) - set((s,))
            if len(other_sets) > 0:
                other = Intersection(*other_sets)
                return Union(*(Intersection(arg, other) for arg in s.args))
            else:
                return Union(*[arg for arg in s.args])

    for s in args:
        if s.is_Complement:
            args.remove(s)
            other_sets = args + [s.args[0]]
            return Complement(Intersection(*other_sets), s.args[1])

#     from sympy.sets.handlers.intersection import intersection_sets

    # At this stage we are guaranteed not to have any
    # EmptySets, FiniteSets, or Unions in the intersection

    # ===== Pair-wise Rules =====
    # Here we depend on rules built into the constituent sets
    args = set(args)
    new_args = True
    while new_args:
        for s in args:
            new_args = False
            for t in args - set((s,)):
                new_set = s.intersection_sets(t)
                # This returns None if s does not know how to intersect
                # with t. Returns the newly intersected set otherwise

                if new_set is not None:
                    new_args = (args - set((s, t))).union(set((new_set,)))
                    break
            if new_args:
                args = new_args
                break

    if len(args) == 1:
        return args.pop()
    else:
        return Intersection(*args, evaluate=False)


def _handle_finite_sets(op, x, y, commutative):
    # Handle finite sets:
    fs_args, other = sift([x, y], lambda x: isinstance(x, FiniteSet), binary=True)
    if len(fs_args) == 2:
        return FiniteSet(*[op(i, j) for i in fs_args[0] for j in fs_args[1]])
    elif len(fs_args) == 1:
        sets = [_apply_operation(op, other[0], i, commutative) for i in fs_args[0]]
        return Union(*sets)
    else:
        return None


def _apply_operation(op, x, y, commutative):
    from sympy.sets import ImageSet
    from sympy import symbols, Lambda
    d = Dummy('d')

    out = _handle_finite_sets(op, x, y, commutative)
    if out is None:
        out = op(x, y)

    if out is None and commutative:
        out = op(y, x)
    if out is None:
        _x, _y = symbols("x y")
        if x.is_set and not y.is_set:
            out = ImageSet(Lambda(d, op(d, y)), x).doit()
        elif not x.is_set and y.is_set:
            out = ImageSet(Lambda(d, op(x, d)), y).doit()
        else:
            out = ImageSet(Lambda((_x, _y), op(_x, _y)), x, y)
    return out


def set_add(x, y):
    from sympy.sets.handlers.add import _set_add
    return _apply_operation(_set_add, x, y, commutative=True)


def set_sub(x, y):
    from sympy.sets.handlers.add import _set_sub
    return _apply_operation(_set_sub, x, y, commutative=False)


def set_mul(x, y):
    from sympy.sets.handlers.mul import _set_mul
    return _apply_operation(_set_mul, x, y, commutative=True)


def set_div(x, y):
    from sympy.sets.handlers.mul import _set_div
    return _apply_operation(_set_div, x, y, commutative=False)


def set_pow(x, y):
    from sympy.sets.handlers.power import _set_pow
    return _apply_operation(_set_pow, x, y, commutative=False)


def set_function(f, x):
    from sympy.sets.handlers.functions import _set_function
    return _set_function(f, x)


class List(Function):
    """
    Return the List Comprehension of a set.
    """

    is_List = True

    @property
    def atomic_dtype(self):
        return self.arg.atomic_dtype

    def _latex(self, p):
        return "[*%s]" % p._print(self.arg)

    @classmethod
    def eval(cls, arg):
        assert arg.is_set
        if arg.is_FiniteSet:
            return FiniteList(*arg.args)

    def __getitem__(self, indices, **kw_args):
        from sympy.tensor.indexed import Indexed, Slice
        if isinstance(indices, (list, tuple)):
            return Indexed(self, *indices, **kw_args)
        elif isinstance(indices, slice):
            start, stop = indices.start, indices.stop
            if start is None:
                start = 0
            if start == stop - 1:
                return Indexed(self, start, **kw_args)
            if start == 0 and stop == self.shape[-1]:
                return self
            return Slice(self, indices, **kw_args)
        else:
            return Indexed(self, indices, **kw_args)

    @property
    def shape(self):
        return (abs(self.arg),) + self.arg.shape

