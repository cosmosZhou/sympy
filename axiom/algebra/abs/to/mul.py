from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self):
    mul = axiom.is_Abs(self)
    args = axiom.is_Mul(mul)
    return Equal(self, Mul(*(abs(arg) for arg in args)))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(abs(x * y))
    
    Eq << Eq[0].this.rhs.apply(algebra.mul.to.abs)

    
if __name__ == '__main__':
    prove()
