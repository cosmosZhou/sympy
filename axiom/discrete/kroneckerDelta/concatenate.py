from util import *


@apply
def apply(W):
    n = W.shape[0]
    k = Symbol(integer=True)

    return Equal(BlockMatrix(BlockMatrix(W.T, ZeroMatrix(n)).T, Lamda[k:n + 1](KroneckerDelta(k, n))),
                 BlockMatrix(BlockMatrix(W, ZeroMatrix(n)).T, Lamda[k:n + 1](KroneckerDelta(k, n))).T)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(domain=Range(2, oo))
    W = Symbol(shape=(n, n), complex=True)
    Eq << apply(W)

    U = Symbol(Eq[0].lhs)
    V = Symbol(Eq[0].rhs)

    Eq << U.this.definition
    Eq << V.this.definition

    i, j = Symbol(domain=Range(0, n + 1))

    Eq <<= V[i, j].this.definition, U[i, j].this.definition

    Eq <<= Eq[-1].this.rhs.apply(algebra.piece.to.kroneckerDelta), Eq[-2].this.rhs.apply(algebra.piece.to.kroneckerDelta)

    Eq << Eq[-1] - Eq[-2]

    Eq << Eq[-1].this.apply(algebra.is_zero.imply.eq)

    Eq << Eq[-1].apply(algebra.eq.imply.eq.lamda, (j,), (i,))

    Eq << Eq[-1].subs(Eq[1]).subs(Eq[2]).reversed


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
