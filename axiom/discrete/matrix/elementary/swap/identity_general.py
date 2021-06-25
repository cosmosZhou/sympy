from util import *


@apply
def apply(x, d, w=None):
    n = x.shape[0]
    assert d.shape == (n,)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    k = Symbol.k(integer=True)

    if w is None:
        w = Symbol.w(Lamda[j, i](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_Swap or w[i, j].definition.is_Swap

    return Equal(x[d @ w[i, j, k]], Lamda[k:n](x[d[k]]) @ w[i, j, k])


@prove
def prove(Eq):
    from axiom import discrete
    n = Symbol.n(domain=Range(2, oo))
    x = Symbol.x(complex=True, shape=(n,))
    d = Symbol.d(integer=True, shape=(n,))

    Eq << apply(x, d)

    k = Eq[-1].rhs.args[1].indices[-1]

    d = Eq[-1].lhs.indices[0].args[0]

    Eq << Eq[-1].rhs.this.subs(Eq[0][k]).this.rhs.apply(discrete.matmul.to.sum)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].lhs.indices[0].this.subs(Eq[0][k]).this.rhs.apply(discrete.matmul.to.sum)

    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    run()
