from sympy import *
from axiom.utility import prove, apply
from axiom import algebra, sets
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self):
    boole, two = axiom.is_Pow(self)
    assert two == 2
    assert boole.is_Bool
    return Equal(self, boole)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
     
    Eq << apply(Bool(x > y) ** 2)
    
    Eq << Eq[0].this.rhs.apply(algebra.bool.to.pow.square)


if __name__ == '__main__':
    prove()

