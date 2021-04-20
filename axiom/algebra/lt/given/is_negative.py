from axiom.utility import prove, apply
from sympy import *
from axiom import algebra
import axiom


@apply
def apply(given):
    x, y = axiom.is_Less(given)
    return Less(x - y, 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    Eq << apply(x < y)
    
    Eq << Eq[0] - y
    

if __name__ == '__main__':
    prove()
