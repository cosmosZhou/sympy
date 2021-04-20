from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self):
    x2, y2 = axiom.is_Substract(self)
    x = axiom.is_Square(x2)
    y = axiom.is_Square(y2)
    return Equal(self, (x - y) * (x + y))


@prove
def prove(Eq):
    
    x = Symbol.x(complex=True)
    y = Symbol.y(complex=True)
    
    Eq << apply(x * x - y * y)
    
    Eq << Eq[0].this.rhs.expand()
    
    
if __name__ == '__main__':
    prove()
