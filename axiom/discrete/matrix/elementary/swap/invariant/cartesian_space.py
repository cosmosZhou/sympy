from util import *

import axiom



@apply
def apply(given, w=None):
    e, S = given.of(Contains)
    x, i = e.args
    n = x.shape[0]
    j = Symbol.j(integer=True)
    if w is None:
        w = Symbol.w(Lamda[j, i](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_Swap or w[i, j].definition.is_Swap

    return Contains(w[i, j] @ x[:n], CartesianSpace(S, n))


@prove
def prove(Eq):
    from axiom import discrete, algebra
    n = Symbol.n(domain=Range(2, oo))
    x = Symbol.x(shape=(n,), integer=True)

    S = Symbol.S(etype=dtype.integer)
    i = Symbol.i(integer=True)
    Eq << apply(Contains(x[i], S))

    Eq << discrete.matrix.elementary.swap.invariant.contains.apply(Eq[1])

    k = Eq[-1].lhs.args[0].indices[-1]

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], (k, 0, n), simplify=False)

    Eq << Eq[2].simplify()

if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
