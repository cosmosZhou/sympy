from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(*given):
    x_less_than_y, neg_x_less_than_y = given
    x, y = axiom.is_StrictLessThan(x_less_than_y)    
    _x, y = axiom.is_StrictLessThan(neg_x_less_than_y)
    assert x == -_x
    return StrictLessThan(abs(x), y)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    Eq << apply(x < y, -x < y)
    
    Eq << Eq[0] - y
    
    Eq << Eq[1] - y
    
    Eq << algebre.is_negative.is_negative.imply.is_positive.apply(Eq[-1], Eq[-2])
    
    Eq << Eq[-1].this.lhs.expand() + x * x
    
    Eq << Eq[-1].reversed
    
    Eq.strict_less_than = algebre.strict_less_than.imply.strict_less_than.sqrt.apply(Eq[-1])
    
    Eq << algebre.strict_less_than.strict_greater_than.imply.strict_greater_than.transit.apply(Eq[0], -Eq[1])
    
    Eq << (Eq[-1] + y) / 2
    
    Eq << algebre.is_positive.imply.equal.abs.apply(Eq[-1])
    
    Eq << Eq.strict_less_than.subs(Eq[-1])
    
    
if __name__ == '__main__':
    prove(__file__)
