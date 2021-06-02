from util import *



@apply
def apply(*given):
    unequality, eq = given
    if not unequality.is_Unequal:
        unequality, eq = eq, unequality
    assert unequality.is_Unequal
    unequality.rhs.is_zero

    assert unequality.lhs.is_Determinant
    divisor = unequality.lhs.arg
    return Unequal(eq.lhs @ Inverse(divisor), eq.rhs @ Inverse(divisor))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True)
    A = Symbol.A(real=True, shape=(n, n), given=True)
    a = Symbol.a(real=True, shape=(n,), given=True)
    b = Symbol.b(real=True, shape=(n,), given=True)
    Eq << apply(Unequal(Determinant(A), 0), Unequal(a @ A, b))

    Eq << ~Eq[-1]

    Eq << algebra.cond.ou.imply.cond.apply(Eq[0], Eq[-1])

    Eq << Eq[-1] @ A

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()
