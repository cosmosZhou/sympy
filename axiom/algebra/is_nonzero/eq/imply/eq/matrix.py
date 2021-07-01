from util import *


@apply
def apply(*given):
    unequality, equality = given
    if not unequality.is_Unequal:
        unequality, equality = equality, unequality
    assert unequality.is_Unequal
    unequality.rhs.is_zero

    assert unequality.lhs.is_Determinant
    divisor = unequality.lhs.arg
    return Equal(equality.lhs @ Inverse(divisor), equality.rhs @ Inverse(divisor))


@prove
def prove(Eq):
    from axiom import discrete, algebra
    n = Symbol.n(integer=True)
    A = Symbol.A(real=True, shape=(n, n))
    a = Symbol.a(real=True, shape=(n,))
    b = Symbol.b(real=True, shape=(n,))
    Eq << apply(Unequal(Determinant(A), 0), Equal(a @ A, b))

    Eq << Eq[1] @ Cofactors(A).T

    Eq << discrete.matrix.determinant.adjugate.apply(A)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << algebra.is_nonzero.eq.imply.eq.scalar.apply(Eq[0], Eq[-1])

    Eq << algebra.is_nonzero.determinant.apply(Eq[0]) * Determinant(A)

    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    run()
