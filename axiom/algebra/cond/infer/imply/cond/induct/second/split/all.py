from util import *


@apply
def apply(f0, suffice, n=None):
    fk, fn = suffice.of(Infer)

    fk, (k, start, _n) = fk.of(All[Tuple])

    assert k.is_integer
    assert fk._subs(k, _n) == fn
    assert fk._subs(k, start) == f0
    diff = _n - n
    if diff:
        assert not diff._has(n)
        fn = fn._subs(n, n - diff)

    n_domain = fn.domain_defined(n)
    assert n_domain.min() >= start

    return fn


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, nonnegative=True)
    k = Symbol(integer=True)
    f, g = Symbol(shape=(oo,), real=True)

    Eq << apply(f[0] > g[0], Infer(All[k:n](f[k] > g[k]), f[n] > g[n]), n=n)

    Eq << Eq[1].this.apply(algebra.infer.to.all, wrt=n)

    Eq << Infer(All[k:n](f[k] > g[k]), All[k:n](f[k] > g[k]), plausible=True)

    Eq <<= Eq[-1] & Eq[1]

    Eq << Eq[-1].this.rhs.apply(algebra.cond.all.imply.all.push_back)

    Eq << algebra.cond.infer.imply.cond.induct.apply(Eq[0], Eq[-1], n=n, start=1)

    Eq << algebra.all.imply.ou.subs.apply(Eq[-1], k, n - 1)

    Eq << Eq[-1].subs(n, n + 1)


if __name__ == '__main__':
    run()
# created on 2019-03-20
