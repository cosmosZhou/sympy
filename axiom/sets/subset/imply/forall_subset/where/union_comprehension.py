from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets, algebre


@apply(imply=True)
def apply(given):
    lhs, rhs = axiom.is_Subset(given)
    assert lhs.is_UNION
    return ForAll(Subset(lhs.function, rhs).simplify(), *lhs.limits)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    x = Symbol.x(shape=(oo,), etype=dtype.complex * n)
    A = Symbol.A(etype=dtype.complex * n)
   
    Eq << apply(Subset(UNION[i:n](x[i]), A))
    
    k = Symbol.k(domain=Interval(0, n - 1, integer=True))
    Eq << Eq[0].this.lhs.bisect(k.set)

    Eq << sets.subset.imply.subset.where.union.apply(Eq[-1])
    
    Eq << algebre.condition.imply.forall.minify.apply(Eq[-1], (k,))

    
if __name__ == '__main__':
    prove(__file__)

