from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(*given):
    x_less_than_a, y_less_than_a = given
    x, a = axiom.is_LessEqual(x_less_than_a)    
    y, _a = axiom.is_LessEqual(y_less_than_a)
    assert a == _a
    return LessEqual(Max(x, y), a)


@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)

    Eq << apply(x <= a, y <= a)
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    
    Eq << algebra.cond.given.ou.apply(Eq[-1])
    
    Eq << Eq[0].apply(algebra.cond.imply.et.ou, cond=x >= y)
    
    Eq << algebra.et.imply.cond.apply(Eq[-1])
    
    Eq.ou = algebra.ou.imply.ou.invert.apply(Eq[-2])
    
    Eq << Eq[1].apply(algebra.cond.imply.et.ou, cond=x >= y)
    
    Eq << algebra.et.imply.cond.apply(Eq[-1])
    
    Eq << algebra.ou.imply.ou.invert.apply(Eq[-1])

    Eq <<= Eq.ou & Eq[-1]
    
    Eq << algebra.et.imply.ou.apply(Eq[-1])
    
    Eq << Eq[-1].this.args[0].apply(algebra.et.imply.ou)

    
if __name__ == '__main__':
    prove()
