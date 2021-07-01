from util import *


@apply
def apply(m, d, w=None, x=None):
    n = d.shape[0]
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)

    assert m >= 0
    if w is None:
        w = Symbol.w(Lamda[j, i](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_Swap or w[i, j].definition.is_Swap

    if x is None:
        x = Symbol.x(shape=(oo,), integer=True, nonnegative=True)
    x = x[:n]

    P = Symbol.P(conditionset(x, Equal(x.set_comprehension(), Range(0, n))))

    return Contains(Lamda[i:n](i) @ MatProduct[i:m](w[i, d[i]]), P)


@prove
def prove(Eq):
    from axiom import discrete, algebra
    n = Symbol.n(domain=Range(2, oo), given=True)
    m = Symbol.m(integer=True, nonnegative=True)
    d = Symbol.d(shape=(n,), integer=True, nonnegative=True)
    x = Symbol.x(shape=(oo,), integer=True, nonnegative=True)

    Eq << apply(m, d, x=x)

    Eq << discrete.matrix.elementary.swap.invariant.permutation.apply(m, d, x=x)

    Eq.ou = algebra.all.imply.ou.subs.apply(Eq[-1], Eq[-1].variable, Eq[2].lhs.args[0])

    Eq << Any[x](Eq.ou.args[1], plausible=True)

    Eq << Eq[-1].this.function.rhs.definition

    Eq << Eq[-1].this.lhs.simplify()

    Eq << ~Eq[-2]

    Eq << Eq[-1].simplify()

    Eq <<= Eq.ou & Eq[-1]

    Eq << algebra.et.imply.cond.apply(Eq[-1], index=0)


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html

