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

Naturals = PositiveIntegers 
Naturals0 = NonnegativeIntegers

UniversalSet = S.UniversalSet
Integers = Interval(S.NegativeInfinity, S.Infinity, integer=True)
del S
