from sympy import *
from axiom.utility import prove, apply
from axiom import algebra
import axiom
from axiom.algebra.eq.eq.imply.eq.sum.absorb.front import absorb_front


@apply
def apply(*imply):
    return absorb_front(Sum, Less, *imply) 


@prove
def prove(Eq):
    k = Symbol.k(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(domain=Interval(a, oo, left_open=True, integer=True))
    g = Function.g(integer=True)
    f = Function.f(integer=True)

    Eq << apply((g(a - 1) < f(a - 1)), Sum[k:a:b](g(k)) < Sum[k:a:b](f(k)))
    
    Eq << algebra.lt.lt.imply.lt.add.apply(Eq[0], Eq[1])
    
    Eq << Eq[2].this.lhs.bisect({a - 1})
    
    Eq << Eq[-1].this.rhs.bisect({a - 1})

    
if __name__ == '__main__':
    prove()

