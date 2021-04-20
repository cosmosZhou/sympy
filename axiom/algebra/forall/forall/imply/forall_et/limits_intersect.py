from axiom.utility import prove, apply
from sympy import *
from axiom import algebra
import axiom
from sympy.concrete.limits import limits_intersect


@apply
def apply(*given):
    forall_a, forall_b = given
    fn, *limits_a = axiom.is_ForAll(forall_a) 
    _fn, *limits_b = axiom.is_ForAll(forall_b)
    
    limits = limits_intersect(limits_a, limits_b)
    return ForAll(fn & _fn, *limits)


@prove
def prove(Eq):
    e = Symbol.e(real=True)
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)
    
    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(ForAll[e:A](f(e) > 0), ForAll[e:B](g(e) > 0))
    
    Eq << algebra.forall_et.given.forall.apply(Eq[-1])
    
    Eq << algebra.forall.given.forall.limits.relaxed.apply(Eq[-2], domain=A)
    
    Eq << algebra.forall.given.forall.limits.relaxed.apply(Eq[-1], domain=B)

if __name__ == '__main__':
    prove()

