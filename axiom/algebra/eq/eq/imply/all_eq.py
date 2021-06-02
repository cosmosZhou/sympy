from util import *
import axiom


@apply
def apply(*given, wrt=None):
    eq_k, eq_n = given
    eq_k.of(Equal)
    eq_n.of(Equal)

    pattern = eq_k._subs(wrt, Wild('k', **wrt.type.dict))
    res = eq_n.match(pattern)
    n, *_ = res.values()
    domain = wrt.domain
    assert n not in domain
    domain |= n.set

    k = wrt.unbounded

    return ForAll[k:domain](eq_k._subs(wrt, k))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))

    k = Symbol.k(domain=Range(0, n))

    Eq << apply(Equal(f[k], g[k]), Equal(f[n], g[n]), wrt=k)

    Eq << algebra.all.given.et.apply(Eq[-1], cond={n})

    Eq << algebra.et.given.conds.apply(Eq[-1])

    Eq << Eq[0].forall((k,))


if __name__ == '__main__':
    run()
