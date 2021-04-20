from sympy import *
from axiom.utility import prove, apply
import axiom


@apply
def apply(given):
    contains, *limits = axiom.is_Exists(given)
    x, B = axiom.is_Contains(contains)
    return Unequal(B, B.etype.emptySet)


@prove
def prove(Eq):
    
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real, given=True)
    e = Symbol.e(real=True)

    Eq << apply(Exists[e:A](Contains(e, B)))
    
    Eq << ~Eq[-1]
    
    Eq << Eq[0].subs(Eq[-1])


if __name__ == '__main__':
    prove()

