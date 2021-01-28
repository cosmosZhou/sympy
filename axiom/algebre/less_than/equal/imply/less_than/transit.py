from axiom.utility import prove, apply
from sympy.core.relational import LessThan, Equal
from sympy import Symbol
from axiom import algebre
import axiom


@apply(imply=True)
def apply(*given):
    a_less_than_x, b_eq_x = given
    a, x = axiom.is_LessThan(a_less_than_x)    
    b, _x = axiom.is_Equal(b_eq_x)
    assert x == _x
    return LessThan(a, b)




@prove
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(a <= x, Equal(b, x))
    
    Eq << Eq[0] + Eq[1].reversed
    
if __name__ == '__main__':
    prove(__file__)
