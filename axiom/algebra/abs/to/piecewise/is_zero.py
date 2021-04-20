from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self):
    x = axiom.is_Abs(self)    
    return Equal(self, Piecewise((x, x > 0), (0, Equal(x, 0)), (-x, True)))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    Eq << apply(abs(x))
    
    Eq << Eq[-1].this.rhs.apply(algebra.piecewise.subs, reverse=True)
    
    Eq << Eq[-1].this.lhs.apply(algebra.abs.to.piecewise)

    
if __name__ == '__main__':
    prove()
