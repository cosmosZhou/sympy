from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given):
    x_imply_P, y_imply_P = given
    p, x = axiom.is_Necessary(x_imply_P)    
    _p, y = axiom.is_Necessary(y_imply_P)
    assert p == _p
    
    return Necessary(p, x | y)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    a = Symbol.a(real=True, given=True)

    Eq << apply(Necessary(a > 0, x > 0), Necessary(a > 0, y > 0))
    
    Eq << Eq[2].reversed
    
    Eq << algebra.sufficient.given.sufficient.split.ou.apply(Eq[-1])
    
    Eq << Eq[-2].reversed
    
    Eq << Eq[-1].reversed
    
    
    
if __name__ == '__main__':
    prove()
