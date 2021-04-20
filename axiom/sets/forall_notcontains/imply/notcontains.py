from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom


@apply
def apply(given):
    notcontains, *limits = axiom.forall_notcontains(given)
    
    e, S = notcontains.args
    
    return NotContains(e, UNION(S, *limits))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(integer=True)
    k = Symbol.k(integer=True)
    
    A = Symbol.A(shape=(oo,), etype=dtype.integer)

    Eq << apply(ForAll[k:n](NotContains(x, A[k])))

    Eq << sets.imply.sufficient.notcontains.induction.apply(Eq[0].function, n)
    
    Eq << algebra.cond.sufficient.imply.cond.transit.apply(Eq[0], Eq[-1])

    
if __name__ == '__main__':
    prove()

