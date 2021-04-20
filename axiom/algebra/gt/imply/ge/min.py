from sympy import *
from axiom.utility import prove, apply
from axiom import algebra


@apply
def apply(given, m):
    assert given.is_Greater
    lhs, rhs = given.args
    return GreaterEqual(Min(lhs, m), Min(rhs, m))


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    
    z = Symbol.z(real=True, given=True)
    Eq << apply(x > y, z)
    Eq << algebra.gt.imply.ge.relax.apply(Eq[0])
    
    Eq << algebra.ge.imply.ge.min.apply(Eq[-1], z)    

if __name__ == '__main__':
    prove()
