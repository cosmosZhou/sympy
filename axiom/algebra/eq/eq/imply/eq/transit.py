from util import *


def transit(*given, reverse=False):
    b_eq_x, x_eq_a = given

    b, x = b_eq_x.of(Equal)    
    _x, a = x_eq_a.of(Equal)
    if x != _x:
        if _x == b:
            b, x = x, b
        elif a == b:
            b, x, _x, a = x, b, a, _x
        elif x == a:
            _x, a = a, _x
    assert x == _x
    if reverse:
        b, a = a, b
    return Equal(b, a)

    
@apply
def apply(*given, reverse=False):
    return transit(*given, reverse=reverse)


@prove
def prove(Eq):
    a = Symbol.a(etype=dtype.real)
    x = Symbol.x(etype=dtype.real)
    b = Symbol.b(etype=dtype.real)

    Eq << apply(Equal(b, x), Equal(x, a))
    
    Eq << Eq[1].subs(Eq[0].reversed)
    
    
if __name__ == '__main__':
    run()
