from util import *


@apply
def apply(x, w=None):
    n = x.shape[0]
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)

    if w is None:
        w = Symbol.w(Lamda[j](Swap(n, 0, j)))

    assert w.shape == (n, n, n)
    assert w[j].definition == Swap(n, 0, j)

    return Equal(Lamda[i:n](x[w[j][i] @ Lamda[i:n](i)]), Lamda[i:n](Piecewise((x[0], Equal(i, j)), (x[j], Equal(i, 0)), (x[i], True))))


@prove
def prove(Eq):
    from axiom import discrete, algebra
    n = Symbol.n(domain=Range(2, oo))
    x = Symbol.x(etype=dtype.integer, shape=(n,))

    Eq << apply(x)

    w = Eq[0].lhs.base

    Eq << discrete.combinatorics.permutation.adjacent.swap1.eq.apply(x, w)

    i, j = Eq[-1].rhs.args[0][1].args
    Eq << Eq[-1].apply(algebra.cond.imply.all.restrict, (i,), (j,))

    _i = i.unbounded
    Eq << Eq[-1].this.find(Lamda).limits_subs(i, _i)

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (_i, 0, n), simplify=False)


if __name__ == '__main__':
    run()
