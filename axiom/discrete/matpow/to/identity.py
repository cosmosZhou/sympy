from util import *


@apply
def apply(w):
    n = w.shape[0]
    i = w.generate_var(integer=True)
    j = w.generate_var({i}, integer=True)

    assert len(w.shape) == 4 and all(s == n for s in w.shape)
    assert w[i, j].is_SwapMatrix or w[i, j].definition.is_SwapMatrix

    return Equal(w[i, j] @ w[i, j], Identity(n))


@prove
def prove(Eq):
    n = Symbol(positive=True, integer=True)
    i, j = Symbol(integer=True)

    assert Identity(n).is_integer
    w = Symbol(Lamda[j, i](SwapMatrix(n, i, j)))

    Eq << apply(w)

    Eq << Eq[0] @ Eq[0]


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-08-24
# updated on 2020-08-24
