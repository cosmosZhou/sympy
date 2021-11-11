from .sets import (Set, Interval, Union, EmptySet, ProductSet,
        Intersection, imageset, conditionset, Complement, SymmetricDifference, CartesianSpace)

from .sets import FiniteSet
from .fancysets import ImageSet, Range, ComplexRegion  # , Reals
from .contains import Element, NotElement
from .subset import Subset, Supset, NotSubset, NotSupset
from .ordinals import Ordinal, OmegaPower, ord0
from ..core.singleton import S
from sympy.sets.fancysets import Reals, ExtendedReals
from sympy.sets.sets import SuperReals, SuperComplexes, HyperReals, HyperComplexes

from sympy.sets.setexpr import Card, Measure
from sympy.core.cache import cacheit

PositiveIntegers = Range(1, S.Infinity)
NonnegativeIntegers = Range(S.Infinity)

Naturals = PositiveIntegers 
Naturals0 = NonnegativeIntegers

Integers = Range(S.NegativeInfinity, S.Infinity)
ExtendedIntegers = Range(S.NegativeInfinity, S.Infinity, left_open=False, right_open=False)
del S