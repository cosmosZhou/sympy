from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, calculus


@apply
def apply(given, *limits):
    lhs, rhs = axiom.is_Greater(given)
    
    return Greater(Integral(lhs, *limits).simplify(), Integral(rhs, *limits).simplify())


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(Greater(f(x), g(x)), (x, a, b))

    Eq << Eq[0].apply(algebra.cond.imply.forall.restrict, (x, a, b))
    
    Eq << calculus.forall_gt.imply.gt.integral.apply(Eq[-1])

if __name__ == '__main__':
    prove()

