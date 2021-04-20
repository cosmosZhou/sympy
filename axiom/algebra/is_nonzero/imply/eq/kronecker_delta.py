from axiom.utility import prove, apply
from sympy import *


@apply
def apply(given):
    assert given.is_Unequal
    assert given.rhs.is_zero
    assert given.lhs.is_KroneckerDelta
    return Equal(*given.lhs.args)


@prove
def prove(Eq):    
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(Unequal(KroneckerDelta(a, b), 0))
    
    Eq << Eq[0].simplify()


if __name__ == '__main__':
    prove()
