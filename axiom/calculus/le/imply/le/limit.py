from sympy import *
from axiom.utility import prove, apply
import axiom


@apply
def apply(given, *limits, simplify=True):
    lhs, rhs = axiom.is_LessEqual(given)
    
    lhs = Limit(lhs, *limits)
    rhs = Limit(rhs, *limits)
    if simplify:
        lhs = lhs.simplify()
        rhs = rhs.simplify()
    return LessEqual(lhs, rhs)


@prove(surmountable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(LessEqual(f(x) / x, g(x) / x), (x, 0))    


if __name__ == '__main__':
    prove()

