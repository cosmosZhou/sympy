from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self): 
    xy = axiom.is_Square(self)
    x, y = axiom.is_Add(xy)
    return Equal(self, x * x + 2 * x * y + y * y)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    Eq << apply((x + y) ** 2)
    
    Eq << Eq[-1].this.lhs.expand()
    
if __name__ == '__main__':
    prove()

from . import st