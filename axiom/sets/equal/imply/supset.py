from axiom.utility import prove, apply

from sympy import *


# given: A = B
# A >> B
@apply
def apply(given):
    assert given.is_Equality
    A, B = given.args
    assert A.is_set and B.is_set
    return Supset(A, B)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)

    equality = Equality(A, B)

    Eq << apply(equality)

    Eq << ~Eq[-1]

    Eq << Eq[-1].subs(equality)


if __name__ == '__main__':
    prove(__file__)

