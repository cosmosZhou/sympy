from util import *


@apply
def apply(x):
    n = x.shape[0]
    i, j = Symbol(domain=Range(n))

    w = Symbol(Lamda[j, i](SwapMatrix(n, i, j)))

    return Equal(x @ w[i, j] @ w[i, j], x)


@prove
def prove(Eq):
    from axiom import discrete, algebra
    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), real=True)
    Eq << apply(x)

    i, j = Eq[0].lhs.indices

    w = Eq[0].lhs.base

    Eq << (x @ w[i, j]).this.subs(Eq[0])
    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << (Eq[-1] @ w[i, j]).this.rhs.subs(Eq[0])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.add.to.piece)


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-11-15
# updated on 2020-11-15