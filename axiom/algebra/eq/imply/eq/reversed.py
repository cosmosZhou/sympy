from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply(simplify=False)
def apply(given):
    lhs, rhs = axiom.is_Equal(given)    
    return Equal(rhs, lhs)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    Eq << apply(Equal(x, y))
    
    Eq << Eq[-1].reversed
    

if __name__ == '__main__':
    prove()

