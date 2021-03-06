from sympy import *
from axiom.utility import prove, apply
import axiom


@apply(imply=True)
def apply(*given):
    b_eq_x, x_eq_a = given
    b, x = axiom.is_Equal(b_eq_x)    
    _x, a = axiom.is_Equal(x_eq_a)
    if x != _x:
        if _x == b:
            b, x = x, b
        elif a == b:
            b, x, _x, a = x, b, a, _x
        elif x == a:
            _x, a = a, _x
    assert x == _x
    return Equal(b, a)


@prove
def prove(Eq):
    a = Symbol.a(etype=dtype.real)
    x = Symbol.x(etype=dtype.real)
    b = Symbol.b(etype=dtype.real)

    Eq << apply(Equal(b, x), Equal(x, a))
    
    Eq << Eq[1].subs(Eq[0].reversed)
    
    
if __name__ == '__main__':
    prove(__file__)
