from axiom.utility import prove, apply
from sympy.core.relational import Equal
from sympy import Symbol
import axiom
from sympy.core.symbol import dtype


@apply(given=True)
def apply(imply, given):
    b_eq_x, x_eq_a = imply, given
    b, x = axiom.is_Equal(b_eq_x)    
    _x, a = axiom.is_Equal(x_eq_a)
    if x != _x:
        if _x == b:
            b, x = x, b
        elif a == b:
            b, x, _x, a = x, b, a, _x 
    assert x == _x
    return Equal(b, a)


@prove
def prove(Eq):
    a = Symbol.a(etype=dtype.real)
    x = Symbol.x(etype=dtype.real)
    b = Symbol.b(etype=dtype.real)

    Eq << apply(Equal(b, x), Equal(x, a))
    
    Eq << Eq[-1].subs(Eq[1].reversed)
    
    
if __name__ == '__main__':
    prove(__file__)
