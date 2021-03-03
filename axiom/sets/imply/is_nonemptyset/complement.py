from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre
# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml


@apply
def apply(a):
    U = a.universalSet
    return Unequal(U // a.set, a.emptySet)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    x = Symbol.x(complex=True, shape=(n,), given=True)

    Eq << apply(x)
    
    Eq << ~Eq[-1]
    
    Eq << sets.is_emptyset.imply.subset.complement.apply(Eq[-1])


if __name__ == '__main__':
    prove(__file__)

