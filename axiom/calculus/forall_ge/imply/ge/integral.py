from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given):
    eq, *limits = axiom.forall_ge(given)
    lhs, rhs = eq.args
    
    return GreaterEqual(Integral(lhs, *limits).simplify(), Integral(rhs, *limits).simplify())


@prove(surmountable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(ForAll[x:a:b](GreaterEqual(f(x), g(x))))
    

if __name__ == '__main__':
    prove()

