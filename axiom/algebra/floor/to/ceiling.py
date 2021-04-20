from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self):
    div = axiom.is_Floor(self)
    plus, d = axiom.is_Divide(div)
    n = plus - (d - 1)

    return Equal(self, ceiling(n / d))


@prove
def prove(Eq):
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True, positive=True)
    Eq << apply(n // d)
    
    Eq << algebra.ceiling.to.floor.apply(Eq[0].rhs).reversed
        
if __name__ == '__main__':
    prove()
