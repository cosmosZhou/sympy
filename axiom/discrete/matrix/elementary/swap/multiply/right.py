from util import *


@apply
def apply(x):
    n = x.shape[0]
    i = Symbol.i(domain=Range(0, n))
    j = Symbol.j(domain=Range(0, n))

    w = Symbol.w(Lamda[j, i](Swap(n, i, j)))

    return Equal(x @ w[i, j] @ w[i, j], x)


@prove
def prove(Eq):
    from axiom import discrete, algebra
    n = Symbol.n(domain=Range(2, oo))
    x = Symbol.x(shape=(n,), real=True)
    Eq << apply(x)

    i, j = Eq[0].lhs.indices

    w = Eq[0].lhs.base

    Eq << (x @ w[i, j]).this.subs(Eq[0])
    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << (Eq[-1] @ w[i, j]).this.rhs.subs(Eq[0])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.function.apply(algebra.add.to.piecewise)


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
