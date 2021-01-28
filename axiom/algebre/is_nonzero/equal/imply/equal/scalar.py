from axiom.utility import prove, apply
from sympy.core.relational import Unequal, Equality
from sympy import Symbol


@apply(imply=True)
def apply(*given):
    unequality, equality = given
    if not unequality.is_Unequality:
        unequality, equality = equality, unequality
    assert unequality.is_Unequality
    unequality.rhs.is_zero
    
    divisor = unequality.lhs
    return Equality(equality.lhs / divisor, equality.rhs / divisor)




@prove
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(Unequal(x, 0), Equality(x * a, b))
    
    Eq << Eq[1] / x
    Eq << (Eq[-1] & Eq[0]).split()


if __name__ == '__main__':
    prove(__file__)
