from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


@apply
def apply(*given):
    x_less_than_a, y_less_than_a = given
    x, a = axiom.is_LessThan(x_less_than_a)    
    y, _a = axiom.is_LessThan(y_less_than_a)
    assert a == _a
    return LessThan(Max(x, y), a)


@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)

    Eq << apply(x <= a, y <= a)
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    
    Eq << algebre.condition.given.ou.apply(Eq[-1])
    
    Eq << Eq[0].bisect(x >= y).split()
    
    Eq.ou = algebre.ou.imply.ou.invert.apply(Eq[-2])
    
    Eq << Eq[1].bisect(x >= y).split()
    
    Eq << algebre.ou.imply.ou.invert.apply(Eq[-1])

    Eq <<= Eq.ou & Eq[-1]
    
    Eq << Eq[-1].astype(Or)
    
    Eq << Eq[-1].this.args[0].astype(Or)

    
if __name__ == '__main__':
    prove(__file__)
