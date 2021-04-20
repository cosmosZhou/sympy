from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given):
    less_than_0, greater_than = given
    x, a = axiom.is_LessEqual(less_than_0)
    y, b = axiom.is_GreaterEqual(greater_than)
    
    return LessEqual((x - a) * (y - b), 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    Eq << apply(x <= a, y >= b)
    
    Eq << Eq[1].reversed   
    
    Eq << algebra.le.le.imply.is_nonnegative.apply(Eq[0], Eq[-1])
    
    Eq << -Eq[-1]
    
    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[2].this.lhs.expand()

        
if __name__ == '__main__':
    prove()

