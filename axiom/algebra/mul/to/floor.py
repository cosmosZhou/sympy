from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self):
    negativeOne, flr = axiom.is_Mul(self, copy=True)
    assert negativeOne == -1
    x = axiom.is_Ceiling(flr)
    return Equal(self, floor(-x))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    Eq << apply(-ceiling(x))
    
    Eq << Eq[0].this.rhs.apply(algebra.floor.to.mul.ceiling)

    
if __name__ == '__main__':
    prove()
