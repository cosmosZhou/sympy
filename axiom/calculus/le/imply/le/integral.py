from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given, *limits):
    lhs, rhs = axiom.is_LessEqual(given)
    
    return LessEqual(Integral(lhs, *limits).simplify(), Integral(rhs, *limits).simplify())


@prove(surmountable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(LessEqual(f(x), g(x)), (x, -oo, oo))
    

if __name__ == '__main__':
    prove()

