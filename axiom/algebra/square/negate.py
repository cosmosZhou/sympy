from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self): 
    args = axiom.is_Square(self)
    args = axiom.is_Add(args)
    
    return Equal(self, Add(*(-arg for arg in args)) ** 2)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    Eq << apply((x - y) ** 2)
    
    Eq << Eq[-1].this.lhs.apply(algebra.square.to.add)
    
    Eq << Eq[-1].this.rhs.apply(algebra.square.to.add)

    
if __name__ == '__main__':
    prove()
