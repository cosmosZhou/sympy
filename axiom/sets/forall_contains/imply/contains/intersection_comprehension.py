from sympy import *
from axiom.utility import prove, apply, given
from axiom import algebra, sets
import axiom


@apply
def apply(given):
    contains, *limits = axiom.forall_contains(given)    
    
    x, A = axiom.is_Contains(contains)
    return Contains(x, INTERSECTION(A, *limits))


@prove
def prove(Eq):
    n = Symbol.n(positive=True, integer=True, given=False)
    x = Symbol.x(integer=True)
    k = Symbol.k(integer=True)
    
    A = Symbol.A(shape=(oo,), etype=dtype.integer)

    Eq << apply(ForAll[k:n](Contains(x, A[k])))
    
    Eq << sets.imply.sufficient.contains.induction.apply(Contains(x, A[k]), n)
    
    Eq << algebra.cond.sufficient.imply.cond.transit.apply(Eq[0], Eq[-1])    

    
if __name__ == '__main__':
    prove()

