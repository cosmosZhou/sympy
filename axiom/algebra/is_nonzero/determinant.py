from util import *


@apply
def apply(given):
    assert given.is_Unequal
    A_det, zero = given.args
    assert A_det.is_Determinant
    assert zero.is_zero
    A = A_det.arg
    return Equal(Cofactors(A).T / Determinant(A), Inverse(A))


@prove
def prove(Eq):
    from axiom import discrete, algebra
    n = Symbol.n(integer=True, positive=True)
    A = Symbol.A(complex=True, shape=(n, n))
    Eq << apply(Unequal(Determinant(A), 0))

    Eq << discrete.matrix.determinant.adjugate.apply(A)

    Eq << algebra.is_nonzero.eq.imply.eq.scalar.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].inverse()

    Eq << algebra.is_nonzero.eq.imply.eq.scalar.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].lhs.args[0].base @ Eq[-1]

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Minor_(linear_algebra)
# https://mathworld.wolfram.com/DeterminantExpansionbyMinors.html
# https://mathworld.wolfram.com/Minor.html
