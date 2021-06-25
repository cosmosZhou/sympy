from util import *


@apply
def apply(n, w=None):
    domain = Range(0, n)
    t = Symbol.t(domain=domain)
    i = Symbol.i(domain=domain)
    j = Symbol.j(domain=domain)
    assert n >= 2
    if w is None:
        w = Symbol.w(Lamda[j, i](Swap(n, i, j)))

    return All(Equal(w[t, i] @ w[t, j] @ w[t, i], w[i, j]), (j, domain // {i, t}))


@prove
def prove(Eq):
    from axiom import discrete, sets, algebra, sets
