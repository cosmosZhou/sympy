from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets, calculus


@apply
def apply(given):
    eq, *limits = axiom.forall_le(given)
    lhs, rhs = eq.args
    
    return LessEqual(Integral(lhs, *limits).simplify(), Integral(rhs, *limits).simplify())


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(ForAll[x:a:b](LessEqual(f(x), g(x))))
    
    Eq << Eq[0].reversed
    
    Eq << calculus.forall_ge.imply.ge.integral.apply(Eq[-1])
    
    Eq << Eq[-1].reversed
    

if __name__ == '__main__':
    prove()

