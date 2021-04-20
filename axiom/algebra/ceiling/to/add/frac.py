from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra

@apply
def apply(self):
    x = axiom.is_Ceiling(self)

    return Equal(self, frac(-x) + x)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    Eq << apply(ceiling(x))
    
    Eq << Eq[0].this.rhs.args[1].definition
    
    Eq << Eq[-1].this.lhs.apply(algebra.ceiling.to.mul)

if __name__ == '__main__':
    prove()