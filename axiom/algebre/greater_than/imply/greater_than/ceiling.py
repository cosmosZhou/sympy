from sympy import *
from axiom.utility import prove, apply
from axiom import algebre
import axiom


@apply(imply=True)
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
    
    Eq << algebre.strict_less_than.imply.less_than.apply(Eq[-1])
    
    Eq << algebre.greater_than.less_than.imply.less_than.transit.apply(Eq[0], Eq[-1])
        
    Eq << Eq[-1].reversed - (y - 1)

    Eq << Eq[-1].this.lhs.apply(algebre.imply.equal.plus.astype.frac)
        
if __name__ == '__main__':
    prove(__file__)



