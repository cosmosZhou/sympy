from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given, *limits):
    lhs, rhs = axiom.is_Less(given)
    
    return Less(Integral(lhs, *limits).simplify(), Integral(rhs, *limits).simplify())


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(Less(f(x), g(x)), (x, a, b))
    
    Eq << Eq[0].apply(algebra.cond.imply.forall.restrict, (x, a, b))
    
    Eq << algebra.forall_lt.imply.lt.integral.apply(Eq[-1])


if __name__ == '__main__':
    prove()

