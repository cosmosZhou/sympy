from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(*given):
    x_less_than_y, a_less_than_b = given
    x, y = axiom.is_LessThan(x_less_than_y)    
    a, b = axiom.is_LessThan(a_less_than_b)
    return LessThan(Min(x, a), Min(y, b))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    Eq << apply(x <= y, a <= b)
    
    Eq << LessThan(Min(x, a), x, plausible=True)
    
    Eq << algebre.less_than.less_than.imply.less_than.transit.apply(Eq[-1], Eq[0])
    
    Eq << LessThan(Min(x, a), a, plausible=True)
    
    Eq << algebre.less_than.less_than.imply.less_than.transit.apply(Eq[1], Eq[-1])
    
    Eq << algebre.less_than.less_than.imply.less_than.min.rhs.apply(Eq[-1], Eq[-3])
    
if __name__ == '__main__':
    prove(__file__)