from sympy import *
from axiom.utility import prove, apply
import axiom


@apply
def apply(given, *limits):
    lhs, rhs = axiom.is_Greater(given)
    
    return GreaterEqual(Limit(lhs, *limits).simplify(), Limit(rhs, *limits).simplify())


@prove(surmountable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(Greater(f(x) / x, g(x) / x), (x, 0))    


if __name__ == '__main__':
    prove()

