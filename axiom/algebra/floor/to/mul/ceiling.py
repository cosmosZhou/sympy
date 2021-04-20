from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self):
    x = axiom.is_Floor(self)

    return Equal(self, -ceiling(-x))


@prove
def prove(Eq):    
    x = Symbol.x(real=True)
    Eq << apply(floor(x))
        
    Eq << -Eq[0]
    
    Eq << Eq[-1].this.rhs.apply(algebra.ceiling.to.mul)
    
if __name__ == '__main__':
    prove()

