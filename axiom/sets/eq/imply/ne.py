from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets, algebra
# given : A & B = A | B => A = B


@apply
def apply(given):
    x_y, _01 = axiom.is_Equal(given)
    x, y = axiom.is_FiniteSet(x_y, 2)
    zero, one = axiom.is_FiniteSet(_01, 2)
    
    assert zero.is_zero
    assert one.is_One
    return Unequal(x, y)


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    
    Eq << apply(Equal({x, y}, {0, 1}))
    
    Eq << ~Eq[-1]
    
    Eq << Eq[0].subs(Eq[-1])

if __name__ == '__main__':
    prove()

