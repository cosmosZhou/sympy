from util import *



@apply(given=None)
def apply(given, wrt=None):
    fn, fn1 = given.of(Suffice)
    if wrt is None:
        wrt = fn.wrt
    assert wrt.is_given is None
    return Equivalent(given, All[wrt:fn](fn1))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True)

    A = Symbol.A(etype=dtype.integer)
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))

    Eq << apply(Suffice(Contains(n, A), Equal(f[n], g[n])), wrt=n)

    Eq.suffice, Eq.necessary = algebra.equivalent.given.cond.apply(Eq[0])

    Eq << Eq.suffice.this.lhs.apply(algebra.suffice.imply.ou)

    Eq << Eq[-1].this.lhs.apply(algebra.ou.imply.all, pivot=1, wrt=n)

    Eq << Eq.necessary.this.lhs.apply(algebra.suffice.given.ou)

    Eq << Eq[-1].this.rhs.apply(algebra.all.imply.ou)


if __name__ == '__main__':
    run()
