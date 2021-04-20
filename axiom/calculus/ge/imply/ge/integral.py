from sympy import *
from axiom.utility import prove, apply
import axiom

from axiom import algebra, sets, calculus


@apply
def apply(given, *limits):
    lhs, rhs = axiom.is_GreaterEqual(given)
    
    return GreaterEqual(Integral(lhs, *limits).simplify(), Integral(rhs, *limits).simplify())


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(GreaterEqual(f(x), g(x)), (x, a, b))

    Eq << Eq[0].apply(algebra.cond.imply.forall.restrict, (x, a, b))    
    
    Eq << calculus.forall_ge.imply.ge.integral.apply(Eq[-1])


if __name__ == '__main__':
    prove()

