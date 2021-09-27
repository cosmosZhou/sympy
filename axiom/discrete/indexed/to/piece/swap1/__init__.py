from util import *


@apply
def apply(x, w=None):
    n = x.shape[0]
    i, j = Symbol(domain=Range(0, n))

    if w is None:
        w = Symbol.w(Lamda[j](SwapMatrix(n, 0, j)))

    assert w.shape == (n, n, n)
    assert w[j].definition == SwapMatrix(n, 0, j)

    return Equal(x[w[j][i] @ Lamda[i:n](i)], Piecewise((x[0], Equal(i, j)), (x[j], Equal(i, 0)), (x[i], True)))


@prove
def prove(Eq):
    from axiom import discrete
    n = Symbol(domain=Range(2, oo))
    x = Symbol(etype=dtype.integer, shape=(n,))

    Eq << apply(x)

    i = Eq[1].rhs.args[2][0].indices[0]
    Eq << Eq[0][i]

    Eq << (Eq[0].lhs[i] @ Eq[1].lhs.indices[0].args[1]).this.args[0].definition

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)

    Eq << Eq[1].lhs.this.subs(Eq[-1])


if __name__ == '__main__':
    run()
from . import helper
