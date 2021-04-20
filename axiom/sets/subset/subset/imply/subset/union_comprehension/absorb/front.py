from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, sets
import axiom
from axiom.algebra.eq.eq.imply.eq.sum.absorb.front import absorb_front


@apply
def apply(*imply): 
    return absorb_front(UNION, Subset, *imply)


@prove
def prove(Eq):
    k = Symbol.k(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(domain=Interval(a, oo, left_open=True, integer=True))
    g = Function.g(etype=dtype.integer)
    f = Function.f(etype=dtype.integer)

    Eq << apply(Subset(g(a - 1), f(a - 1)), Subset(UNION[k:a:b](g(k)), UNION[k:a:b](f(k))))
    
    Eq << sets.subset.subset.imply.subset.union.apply(Eq[0], Eq[1])    

    
if __name__ == '__main__':
    prove()

