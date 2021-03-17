from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


@apply
def apply(*given):
    x_less_than_a, y_less_than_a = given
    x, a = axiom.is_GreaterThan(x_less_than_a)    
    y, _a = axiom.is_GreaterThan(y_less_than_a)
    assert a == _a
    return GreaterThan(Min(x, y), a)


@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)

    Eq << apply(x >= a, y >= a)
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    
    Eq << algebre.cond.given.ou.apply(Eq[-1])
    
    Eq << ~Eq[-1]
    
    Eq << algebre.cond.cond.imply.cond.apply(Eq[0], Eq[-1], invert=True)
    
    Eq << algebre.cond.cond.imply.cond.apply(Eq[1], Eq[-1], invert=True)
    
    
    
if __name__ == '__main__':
    prove(__file__)
