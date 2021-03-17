from sympy import *
from axiom.utility import prove, apply
from axiom import algebre


@apply
def apply(*given):
    unequality, eq = given
    assert eq.is_Unequality
    assert unequality.is_Unequality
    unequality.rhs.is_zero
    
    divisor = unequality.lhs
    return Unequal(eq.lhs / divisor, eq.rhs / divisor)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(Unequal(x, 0), Unequal(x * a, b))
    
    Eq << Eq[1] / x
    
    Eq <<= Eq[-1] & Eq[0]
    
    Eq << algebre.et.imply.cond.apply(Eq[-1])


if __name__ == '__main__':
    prove(__file__)
