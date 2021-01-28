from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets


@apply(imply=True)
def apply(given):
    lhs, rhs = axiom.is_Supset(given)
    assert rhs.is_UNION
    return ForAll(Supset(lhs, rhs.function, ).simplify(), *rhs.limits)

@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    x = Symbol.x(shape=(oo,), etype=dtype.complex * n)
    A = Symbol.A(etype=dtype.complex * n)
   
    Eq << apply(Supset(A, UNION[i:n](x[i])))
    
    Eq << Eq[0].reversed
    
    Eq << sets.subset.imply.forall_subset.where.union_comprehension.apply(Eq[-1])
    
    Eq << Eq[-1].reversed
    
if __name__ == '__main__':
    prove(__file__)

