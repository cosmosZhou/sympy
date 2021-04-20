from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given):
    x_imply_P, y_imply_P = given
    x, p = axiom.is_Sufficient(x_imply_P)    
    y, _p = axiom.is_Sufficient(y_imply_P)
    assert p == _p
    
    return Sufficient(x | y, p)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    a = Symbol.a(real=True, given=True)

    Eq << apply(Sufficient(x > 0, a > 0), Sufficient(y > 0, a > 0))
    
    Eq << Eq[-1].apply(algebra.sufficient.given.ou)
    
    Eq << Eq[0].apply(algebra.sufficient.imply.ou)
    
    Eq << Eq[1].apply(algebra.sufficient.imply.ou)
    
    Eq <<= Eq[-2] & Eq[-1]
    
    
    
if __name__ == '__main__':
    prove()
