from sympy import *
from axiom.utility import prove, apply
from axiom import algebre
import axiom


@apply(imply=True)
def apply(given):
    x, y = axiom.is_LessThan(given)
    assert x.is_integer
    assert y.is_real

    return LessThan(x, floor(y))


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(real=True, given=True)
    
    Eq << apply(x <= y)
    
    Eq << ~Eq[1]
    
    Eq << algebre.strict_greater_than.imply.greater_than.integer.apply(Eq[-1])
    
    Eq << algebre.less_than.greater_than.imply.greater_than.transit.apply(Eq[0], Eq[-1])
        
    Eq << Eq[-1] - floor(y)
    
    Eq << Eq[-1].this.lhs.apply(algebre.imply.equal.plus.astype.frac)
        
if __name__ == '__main__':
    prove(__file__)



