from util import *


@apply
def apply(*given):
    b_greater_than_x, x_greater_than_a = given
    b, x = b_greater_than_x.of(GreaterEqual)    
    _x, a = x_greater_than_a.of(GreaterEqual)
    if b == a:
        b, x, _x, a = _x, a, b, x    
    assert x == _x
    return GreaterEqual(b, a)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(b >= x, x >= a)
    
    Eq << Eq[0] + Eq[1]  
    
    Eq << Eq[-1] - x
    
    
if __name__ == '__main__':
    run()
