from util import *


@apply
def apply(n, w=None):
    i, j = Symbol(domain=Range(0, n))

    assert n >= 2
    if w is None:
        w = Symbol.w(Lamda[j, i](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)

    return All(Equal(w[0, i] @ w[0, j] @ w[0, i], w[i, j]), (j, Range(1, n) - {i}))


@prove
def prove(Eq):
    from axiom import discrete
    n = Symbol(domain=Range(2, oo))
    assert 0 in Range(0, n)
    Eq << apply(n)
    w = Eq[0].lhs.base
    Eq << discrete.imply.all_eq.swap2.eq_general.apply(n, w=w)

    w_ti, *_ = Eq[-1].expr.lhs.args
    t, i = w_ti.indices

    Eq << Eq[-1].subs(t, 0)


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
