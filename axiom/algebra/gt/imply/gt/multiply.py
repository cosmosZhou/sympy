from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given, factor):
    lhs, rhs = axiom.is_Greater(given)
    
    assert factor > 0
    
    return Greater(lhs * factor, rhs * factor)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    k = Symbol.k(real=True, given=True, positive=True)
    
    Eq << apply(Greater(x, y), k)
    
    Eq << Greater(k, 0, plausible=True)
    
    Eq << Eq[0] - y
    
    Eq << algebra.is_positive.is_positive.imply.is_positive.mul.apply(Eq[-2], Eq[-1])
    
    Eq << Eq[-1].this.lhs.expand()
    
    Eq << algebra.is_positive.imply.gt.apply(Eq[-1])


if __name__ == '__main__':
    prove()

