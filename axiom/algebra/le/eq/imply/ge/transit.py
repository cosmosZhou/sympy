from axiom.utility import prove, apply
from sympy import *
from axiom import algebra
import axiom


@apply
def apply(*given):
    a_less_than_x, b_eq_x = given
    a, x = axiom.is_LessEqual(a_less_than_x)    
    b, _x = axiom.is_Equal(b_eq_x)
    assert x == _x
    return GreaterEqual(b, a)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(a <= x, Equal(b, x))
    
    Eq << Eq[0] + Eq[1].reversed

    Eq << Eq[-1].reversed
    
    Eq << Eq[-1].this.apply(algebra.ge.simplify.common_terms)
    
if __name__ == '__main__':
    prove()
