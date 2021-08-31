from .sets import (Set, Interval, Union, EmptySet, ProductSet,
        Intersection, imageset, conditionset, Complement, SymmetricDifference, CartesianSpace)

from .sets import FiniteSet
from .fancysets import ImageSet, Range, ComplexRegion  # , Reals
from .contains import Element, NotElement
from .subset import Subset, Supset, NotSubset, NotSupset
from .ordinals import Ordinal, OmegaPower, ord0
from ..core.singleton import S
from sympy.sets.fancysets import Reals

from sympy.sets.setexpr import Card, Measure

PositiveIntegers = Range(1, S.Infinity)
NonnegativeIntegers = Range(0, S.Infinity)
# NegativeIntegers = Range(S.NegativeInfinity, 0)
# NonpositiveIntegers = Range(S.NegativeInfinity, 1)

Naturals = PositiveIntegers 
Naturals0 = NonnegativeIntegers

Integers = Range(S.NegativeInfinity, S.Infinity)
del S
