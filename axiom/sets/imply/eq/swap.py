from util import *


@apply
def apply(x, i=None, j=None):
    assert len(x.shape) == 1

    assert x.dtype.is_set
    if i is None:
        i = Symbol.i(integer=True)

    if j is None:
        j = Symbol.j(integer=True)

    return Equal(swap[i, j](swap[i, j](x)), x)


def swap(p, *indices):
    n = p.shape[0]
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    w = Symbol.w(Lamda[j, i](Swap(n, i, j)))

    (i,), (j,) = indices
    k = Symbol.k(integer=True)

    d = Lamda[k:n](k) @ w[i, j]
    return Lamda[k:n](p[d[k]])


swap = Function.swap(eval=swap)


@prove
def prove(Eq):
    from axiom import discrete
    n = Symbol.n(positive=True, integer=True)

    x = Symbol.x(shape=(n,), etype=dtype.integer)

    Eq << apply(x)

    (i,), (j,) = Eq[0].lhs.limits

    Eq << Eq[-1].this.lhs.arg.defun()

    Eq << Eq[-1].this.lhs.defun()

    w = Eq[-1].lhs.function.indices[0].args[1].base

    Eq << discrete.matrix.elementary.swap.identity.apply(w[i, j], left=False, w=w, reference=False)

    k = Eq[-1].rhs.args[1].indices[-1]

    Eq << Eq[-2].lhs.function.index.this.subs(Eq[-1])

    Eq << discrete.matrix.elementary.swap.square.apply(w)

    Eq << Eq[-1][k].T

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)

    Eq << Eq[-1].this(k).rhs.simplify()

    Eq << Eq[2].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
