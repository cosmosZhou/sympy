from sympy import *
from axiom.utility import prove, apply
from axiom import algebra
import axiom


@apply
def apply(*imply): 
    cond, forall = imply
    fn, *limits = axiom.is_ForAll(forall)
    k, a, b = axiom.limit_is_Interval(limits)
    assert fn._subs(k, b) == cond
    
    return ForAll[k:a:b + 1](fn)


@prove
def prove(Eq):
    k = Symbol.k(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(domain=Interval(a, oo, left_open=True, integer=True))
    g = Function.g(integer=True)

    Eq << apply((g(b) > 0), ForAll[k:a:b](g(k) > 0))
    
    Eq << algebra.forall.given.et.apply(Eq[-1], cond={b})
    
    Eq << algebra.et.given.cond.apply(Eq[-1])
    

    
if __name__ == '__main__':
    prove()

