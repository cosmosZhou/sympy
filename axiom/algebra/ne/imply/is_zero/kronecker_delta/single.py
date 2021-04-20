from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given):
    lhs, rhs = axiom.is_Unequal(given)
    return Equal(KroneckerDelta(lhs, rhs), 0)


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    Eq << apply(Unequal(x, y))
    
    Eq << Eq[1].this.lhs.astype(Piecewise)    


if __name__ == '__main__':
    prove()
