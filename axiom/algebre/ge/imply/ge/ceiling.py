from sympy import *
from axiom.utility import prove, apply
from axiom import algebre
import axiom


@apply
def apply(given):
    x, y = axiom.is_GreaterThan(given)
    assert x.is_integer
    assert y.is_real

    return GreaterThan(x, ceiling(y))


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(real=True, given=True)
    
    Eq << apply(x >= y)
    
    Eq << ~Eq[1]
    
    Eq << algebre.lt.imply.le.strengthen.apply(Eq[-1])
    
    Eq << algebre.ge.le.imply.le.transit.apply(Eq[0], Eq[-1])
        
    Eq << Eq[-1].reversed - (y - 1)

    Eq << Eq[-1].this.lhs.apply(algebre.plus.astype.frac)
        
if __name__ == '__main__':
    prove(__file__)



