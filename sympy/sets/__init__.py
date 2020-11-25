from .sets import (Set, Interval, Union, EmptySet, FiniteSet, ProductSet,
        Intersection, imageset, Complement, SymmetricDifference)
from .fancysets import ImageSet, Range, ComplexRegion, Reals
from .contains import Contains
from .conditionset import ConditionSet
from .ordinals import Ordinal, OmegaPower, ord0
from ..core.singleton import S
Reals = S.Reals
PositiveIntegers = Interval(1, S.Infinity, integer=True)
NonnegativeIntegers = Interval(0, S.Infinity, integer=True)
# NegativeIntegers = Interval(S.NegativeInfinity, -1, integer=True)
# NonpositiveIntegers = Interval(S.NegativeInfinity, 0, integer=True)

Naturals = PositiveIntegers 
Naturals0 = NonnegativeIntegers

Integers = Interval(S.NegativeInfinity, S.Infinity, integer=True)
del S
