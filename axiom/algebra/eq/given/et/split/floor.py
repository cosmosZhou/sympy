from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given):
    y, floor_x = axiom.is_Equal(given)
    if not floor_x.is_Floor:
        y, floor_x = floor_x, y
    assert y.is_integer
    x = axiom.is_Floor(floor_x)
    return And(x - 1 < y, y <= x)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(integer=True)

    Eq << apply(Equal(y, floor(x)))
    
    Eq << Eq[1].apply(algebra.lt.le.imply.eq)
    
    
if __name__ == '__main__':
    prove()
