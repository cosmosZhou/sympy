from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self):
    div = axiom.is_Floor(self)
    sub_x_1, two = axiom.is_Divide(div)
    assert two == 2
    x = sub_x_1 + 1

    return Equal(self, x - x // 2 - 1)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    Eq << apply((x - 1) // 2)
    
    Eq << Eq[-1].this.lhs.apply(algebra.floor.to.ceiling)
    
    Eq << Eq[-1].this.lhs.apply(algebra.ceiling.to.add.frac)
    
    Eq << Eq[-1] - x / 2
    
    Eq << Eq[-1].this.rhs.apply(algebra.add.to.frac)
    
    Eq << Eq[-1].this.lhs.apply(algebra.frac.half)
    
    

    
if __name__ == '__main__':
    prove()

