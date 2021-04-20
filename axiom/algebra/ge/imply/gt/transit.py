from axiom.utility import prove, apply
from sympy import *
from axiom import algebra


@apply
def apply(given, lower_bound):
    assert given.is_GreaterEqual
    lhs, rhs = given.args
    assert rhs > lower_bound
    return Greater(lhs, lower_bound)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    Eq << apply(x >= y, y - 1)
    
    Eq << Greater(y, y - 1, plausible=True)
    
    Eq << algebra.ge.gt.imply.gt.transit.apply(Eq[0], Eq[-1])
    

if __name__ == '__main__':
    prove()
