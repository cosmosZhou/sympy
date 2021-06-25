from util import *


@apply
def apply(*given):
    a_less_than_x, x_less_than_b = given
    a, x = a_less_than_x.of(Equal)    
    b, y = x_less_than_b.of(GreaterEqual)

    return GreaterEqual(a + b, x + y)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)
    y = Symbol.y(real=True)

    Eq << apply(Equal(a, x), y >= b)
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq << Eq[-1] - x
    
    
    
if __name__ == '__main__':
    run()
