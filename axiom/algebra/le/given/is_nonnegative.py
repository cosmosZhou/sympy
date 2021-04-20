from axiom.utility import prove, apply
from sympy import *
from axiom import algebra
import axiom


@apply
def apply(given):
    x, y = axiom.is_LessEqual(given)
    return GreaterEqual(y - x, 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    Eq << apply(x <= y)
    
    Eq << Eq[1] - y
    
    Eq << -Eq[-1]
    

if __name__ == '__main__':
    prove()
