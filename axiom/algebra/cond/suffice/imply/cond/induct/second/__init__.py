from util import *


@apply
def apply(*given, n=None, k=None, hypothesis=False):
    f0, sufficient = given

    fk, fn = sufficient.of(Suffice)

    start, _n = k.domain.of(Range)

    assert fk._subs(k, _n) == fn
    assert fk._subs(k, start) == f0
    diff = _n - n
    if diff:
        assert not diff._has(n)
        fn = fn._subs(n, n - diff)

    domain = fn.domain_defined(n)
    assert domain >= start

    if hypothesis:
        return fn, fk
    return fn


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, nonnegative=True)
    k = Symbol.k(domain=Range(0, n))
    f = Symbol.f(shape=(oo,), real=True)
    g = Symbol.g(shape=(oo,), real=True)

    Eq << apply(f[0] > g[0], Suffice(f[k] > g[k], f[n] > g[n]), n=n, k=k, hypothesis=True)

    Eq << Eq[1].this.lhs.forall((k,))

    Eq << algebra.cond.suffice.imply.cond.induct.second.split.all.apply(Eq[0], Eq[-1], n=n)

    Eq << Eq[2].subs(n, k)


if __name__ == '__main__':
    run()

from . import split
