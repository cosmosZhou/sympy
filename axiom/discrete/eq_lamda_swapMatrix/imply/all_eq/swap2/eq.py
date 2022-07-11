from util import *


@apply
def apply(eq_w):
    ((i, j), (S[j], S[0], n), (S[i], S[0], S[n])), w = eq_w.of(Equal[Lamda[SwapMatrix]])
    i, j = Symbol(domain=Range(n))
    assert n >= 2
    return All(Equal(w[0, i] @ w[0, j] @ w[0, i], w[i, j]), (j, Range(1, n) - {i}))


@prove
def prove(Eq):
    from axiom import discrete

    n = Symbol(domain=Range(2, oo))
    w = Symbol(integer=True, shape=(n, n, n, n))
    i, j = Symbol(integer=True)
    Eq << apply(Equal(w, Lamda[j:n, i:n](SwapMatrix(n, i, j))))

    w = Eq[0].lhs
    Eq << discrete.eq_lamda_swapMatrix.imply.all_eq.swap2.eq_general.apply(Eq[0])

    w_ti, *_ = Eq[-1].expr.lhs.args
    t, i = w_ti.indices
    Eq << Eq[-1].subs(t, 0)

    


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-08-23
# updated on 2022-04-01
