from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given):
    is_nonnegative, less_than = given
    if not less_than.is_Less:
        less_than, is_nonnegative = given
    
    x = axiom.is_nonnegative(is_nonnegative)
    _x, M = axiom.is_Less(less_than)
    assert x == _x
    
    return Equal(x, frac(x))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    
    Eq << apply(x >= 0, x < 1)
    
    Eq << Eq[-1].this.rhs.definition.reversed
    
    Eq << algebra.imply.le.floor.apply(x)
    
    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[-1], Eq[1])
    
    Eq << algebra.lt.imply.le.strengthen.apply(Eq[-1])
    
    Eq << algebra.imply.gt.floor.apply(x)
    
    Eq << algebra.gt.ge.imply.gt.transit.apply(Eq[-1], Eq[0] - 1)
    
    Eq << algebra.gt.imply.ge.strengthen.apply(Eq[-1])
    
    Eq <<= Eq[-4] & Eq[-1]

        
if __name__ == '__main__':
    prove()
