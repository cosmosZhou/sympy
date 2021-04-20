from axiom.utility import prove, apply
from sympy.core.relational import GreaterEqual, LessEqual, Less, Equal
from sympy import Symbol
import axiom
from axiom import algebra


@apply
def apply(*given):
    b_greater_than_x, x_eq_a = given
    b, x = axiom.is_Greater(b_greater_than_x)    
    _x, a = axiom.is_Equal(x_eq_a)
    assert x == _x
    return Less(a, b)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(b > x, Equal(x, a))
    
    Eq << algebra.gt.eq.imply.gt.transit.apply(Eq[0], Eq[1])
    
    Eq << Eq[-1].reversed
    
    
if __name__ == '__main__':
    prove()
