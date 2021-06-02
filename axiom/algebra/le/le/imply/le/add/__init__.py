from util import *
import axiom


@apply
def apply(*given):
    a_less_than_b, x_less_than_y = given
    a, b = a_less_than_b.of(LessEqual)    
    x, y = x_less_than_y.of(LessEqual)
    return LessEqual(a + x, b + y)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)
    y = Symbol.y(real=True)

    Eq << apply(a <= b, x <= y)
    
    Eq << Eq[0] + Eq[1]   
    
    
if __name__ == '__main__':
    run()

from . import abs
