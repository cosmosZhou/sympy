from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self):
    div = axiom.is_Ceiling(self)
    n, d = axiom.is_Divide(div)

    return Equal(self, (n - 1) // d + 1)


@prove
def prove(Eq):
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True)
    Eq << apply(ceiling(n / d))
    
    Eq << Eq[0].this.lhs.apply(algebra.ceiling.to.floor)
    
    Eq << Eq[-1].this.lhs.apply(algebra.floor.to.add.quotient)
    
    
if __name__ == '__main__':
    prove()
