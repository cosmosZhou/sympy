from axiom.utility import prove, apply
from sympy import *

import axiom
from axiom import sets


@apply
def apply(imply):
    lhs, rhs = axiom.is_Subset(imply)
    assert lhs.is_UNION
    return ForAll(Subset(lhs.function, rhs).simplify(), *lhs.limits)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    x = Symbol.x(shape=(oo,), etype=dtype.complex * n)
    A = Symbol.A(etype=dtype.complex * n)
   
    Eq << apply(Subset(UNION[i:n](x[i]), A))
    
    Eq << sets.forall_subset.imply.subset.union_comprehension.apply(Eq[-1])

    
if __name__ == '__main__':
    prove()

