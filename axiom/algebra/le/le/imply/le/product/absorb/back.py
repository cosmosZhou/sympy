from sympy import *
from axiom.utility import prove, apply
from axiom import algebra
import axiom
from axiom.algebra.eq.eq.imply.eq.sum.absorb.back import absorb_back


@apply
def apply(*imply): 
    return absorb_back(Product, LessEqual, *imply, criteria=lambda cond: cond.lhs >= 0)


@prove
def prove(Eq):
    k = Symbol.k(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(domain=Interval(a, oo, left_open=True, integer=True))
    g = Function.g(integer=True, nonnegative=True)
    f = Function.f(integer=True)
    
    Eq << apply((g(b) <= f(b)), Product[k:a:b](g(k)) <= Product[k:a:b](f(k)))
    
    Eq << algebra.le.le.imply.le.multiply.apply(Eq[0], Eq[1])
    
    Eq << Eq[2].this.lhs.bisect({b})
    
    Eq << Eq[-1].this.rhs.bisect({b})

    
if __name__ == '__main__':
    prove()

