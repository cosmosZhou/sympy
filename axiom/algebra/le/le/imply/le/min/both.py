from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given):
    x_less_than_y, a_less_than_b = given
    x, y = axiom.is_LessEqual(x_less_than_y)    
    a, b = axiom.is_LessEqual(a_less_than_b)
    return LessEqual(Min(x, a), Min(y, b))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    Eq << apply(x <= y, a <= b)
    
    Eq << LessEqual(Min(x, a), x, plausible=True)
    
    Eq << algebra.le.le.imply.le.transit.apply(Eq[-1], Eq[0])
    
    Eq << LessEqual(Min(x, a), a, plausible=True)
    
    Eq << algebra.le.le.imply.le.transit.apply(Eq[1], Eq[-1])
    
    Eq << algebra.le.le.imply.le.min.rhs.apply(Eq[-1], Eq[-3])
    
if __name__ == '__main__':
    prove()
