from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(*given):
    is_nonnegative, less_than = given
    if not less_than.is_StrictLessThan:
        less_than, is_nonnegative = given
    
    x = axiom.is_nonnegative(is_nonnegative)
    _x, M = axiom.is_StrictLessThan(less_than)
    assert x == _x
    
    return Equal(x, frac(x))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    
    Eq << apply(x >= 0, x < 1)
    
    Eq << Eq[-1].this.rhs.definition.reversed
    
    Eq << algebre.imply.less_than.floor.apply(x)
    
    Eq << algebre.less_than.strict_less_than.imply.strict_less_than.transit.apply(Eq[-1], Eq[1])
    
    Eq << algebre.strict_less_than.imply.less_than.strengthen.apply(Eq[-1])
    
    Eq << algebre.imply.strict_greater_than.floor.apply(x)
    
    Eq << algebre.strict_greater_than.greater_than.imply.strict_greater_than.transit.apply(Eq[-1], Eq[0] - 1)
    
    Eq << algebre.strict_greater_than.imply.greater_than.strengthen.apply(Eq[-1])
    
    Eq <<= Eq[-4] & Eq[-1]

        
if __name__ == '__main__':
    prove(__file__)
