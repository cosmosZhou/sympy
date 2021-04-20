from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given):
    x_less_than_a, y_less_than_b = given
    abs_x, a = axiom.is_LessEqual(x_less_than_a)    
    abs_y, b = axiom.is_LessEqual(y_less_than_b)
    
    x = axiom.is_Abs(abs_x)
    y = axiom.is_Abs(abs_y)
    
    return LessEqual(abs(x + y), a + b)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    Eq << apply(abs(x) <= a, abs(y) <= b)
    
    Eq << algebra.le.given.cond.split.abs.apply(Eq[-1])
    
    Eq << algebra.le.imply.cond.split.abs.apply(Eq[0])
    
    Eq << algebra.le.imply.cond.split.abs.apply(Eq[1])
    
    Eq <<= Eq[-4] + Eq[-2], Eq[-3] + Eq[-1]
    
    
if __name__ == '__main__':
    prove()
