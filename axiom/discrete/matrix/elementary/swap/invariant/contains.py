from util import *


@apply
def apply(given, w=None, n=None):
    e, S = given.of(Contains)
    x, i = e.args

    if n is None:
        n = x.shape[0]

    j = Symbol.j(integer=True)
    if w is None:
        w = Symbol.w(Lamda[j, i](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_Swap or w[i, j].definition.is_Swap
    k = Symbol.k(integer=True)

    return Contains(w[i, j, k] @ x[:n], S)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(domain=Range(2, oo))
    x = Symbol.x(shape=(n,), integer=True)

    S = Symbol.S(etype=dtype.integer)
    i = Symbol.i(integer=True)
    Eq << apply(Contains(x[i], S))

    i, j, k = Eq[-1].lhs.args[0].indices

    Eq << (Eq[0].lhs[k] @ x).this.args[0].definition

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[2].subs(Eq[-1])

    Eq <<= Eq[1].subs(i, j), Eq[1].subs(i, k)

    Eq << sets.contains.contains.imply.contains.piecewise.apply(Eq[1], Eq[-1], Eq[-2], piecewise=Eq[-3].lhs)


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
