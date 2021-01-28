from sympy.core.relational import Equality, Unequal
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.sets import Union, Intersection
from sympy import Symbol
from axiom import sets, algebre
from sympy.concrete.summations import Sum
from sympy.functions.elementary.piecewise import Piecewise
from sympy.sets.contains import Contains
from sympy.sets.conditionset import conditionset
from sympy.concrete.forall import ForAll

# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml


@apply(imply=True)
def apply(a):
    U = a.universalSet
    return Unequal(U - a.set, a.emptySet)




@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    x = Symbol.x(complex=True, shape=(n,), given=True)

    Eq << apply(x)
    
    Eq << ~Eq[-1]
    
    Eq << sets.is_emptyset.imply.subset.complement.apply(Eq[-1])


if __name__ == '__main__':
    prove(__file__)

