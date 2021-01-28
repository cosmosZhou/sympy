from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


@apply(imply=True)
def apply(given):
    lhs, rhs = axiom.is_StrictLessThan(given)
    
    b0, e0 = axiom.is_Power(lhs)
    b1, e1 = axiom.is_Power(rhs)
    assert e0.is_even
    assert e1.is_even
    
    e0 //= 2    
    e1 //= 2
    
    return StrictLessThan(abs(b0 ** e0), abs(b1 ** e1))


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    
    Eq << apply(StrictLessThan(x * x, y * y))

    Eq << ~Eq[1]
    
    Eq << Eq[-1] * Eq[-1]
    
    Eq <<= Eq[-1] & Eq[0]

if __name__ == '__main__':
    prove(__file__)

