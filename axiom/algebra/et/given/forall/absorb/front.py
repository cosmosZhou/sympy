from sympy import *
from axiom.utility import prove, apply
from axiom import algebra
import axiom


@apply
def apply(imply): 
    cond, forall = axiom.is_And(imply)
    fn, *limits = axiom.is_ForAll(forall)
    k, a, b = axiom.limit_is_Interval(limits)
    assert fn._subs(k, a - 1) == cond
    
    return ForAll[k:a - 1:b](fn)


@prove
def prove(Eq):
    k = Symbol.k(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(domain=Interval(a, oo, left_open=True, integer=True))
    g = Function.g(integer=True)

    Eq << apply((g(a - 1) > 0) & ForAll[k:a:b](g(k) > 0))
    
    Eq << algebra.forall.imply.et.split.apply(Eq[1], cond={a - 1})

    
if __name__ == '__main__':
    prove()

