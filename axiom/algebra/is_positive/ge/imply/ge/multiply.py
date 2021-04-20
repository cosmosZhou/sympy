from axiom.utility import prove, apply
from sympy.core.relational import Equal, Greater, Less,\
    GreaterEqual
from sympy import Symbol
import axiom
from sympy.functions.elementary.piecewise import Piecewise
from axiom import algebra, sets


@apply
def apply(*given):
    is_positive_x, strict_less_than = given
    x = axiom.is_positive(is_positive_x)
    lhs, rhs = axiom.is_GreaterEqual(strict_less_than)
    return GreaterEqual(lhs * x, rhs * x)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    Eq << apply(x > 0, a >= b)
    
    Eq << Eq[1] - b
    
    Eq << algebra.is_positive.is_nonnegative.imply.is_nonnegative.apply(Eq[0], Eq[-1])
    
    Eq << Eq[-1].this.lhs.expand()
    
    Eq << Eq[-1] + b * x

    
if __name__ == '__main__':
    prove()
