from util import *


@apply
def apply(n):
    k = Symbol.k(integer=True)

    return Equal(Lamda[k:n + 1](KroneckerDelta(k, n)), BlockMatrix(ZeroMatrix(n), 1))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(domain=Range(2, oo))
    Eq << apply(n)

    U = Symbol.U(Eq[0].lhs)
    V = Symbol.V(Eq[0].rhs)

    assert V.is_complex
    assert V.is_real
    assert V.is_rational
    assert V.is_integer

    Eq << U.this.definition
    Eq << V.this.definition

    i = Symbol.i(domain=Range(0, n + 1))

    Eq << Eq[-1][i]

    Eq << U[i].this.definition

    Eq << Eq[-2].this.rhs.astype(KroneckerDelta)

    Eq << Eq[-2] - Eq[-1]

    Eq << algebra.is_zero.imply.eq.apply(Eq[-1])

    Eq << Eq[-1].apply(algebra.eq.imply.eq.lamda, (i,), simplify=False)

    Eq << Eq[-1].subs(Eq[1]).subs(Eq[2])


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
