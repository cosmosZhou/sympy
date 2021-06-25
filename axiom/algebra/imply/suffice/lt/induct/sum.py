from util import *


@apply(given=None)
def apply(given, limit):
    xk, yk = given.of(Less)
    k, a, b = limit
    assert xk._has(k)
    assert yk._has(k)

    return Suffice(All[k:a:b](xk < yk), Sum[k:a:b](xk) < Sum[k:a:b](yk))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True, given=False)
    k = Symbol.k(integer=True)

    y = Symbol.y(shape=(oo,), integer=True)
    x = Symbol.x(shape=(oo,), integer=True)

    Eq << apply(x[k] < y[k], (k, 0, n))

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << algebra.suffice.imply.suffice.et.both_sided.apply(Eq[0], cond=x[n] < y[n])

    Eq << Eq[-1].this.lhs.apply(algebra.et.given.all.absorb.back)

    Eq << Eq[-1].this.rhs.apply(algebra.lt.lt.imply.lt.sum.absorb.back)

    Eq << Eq.induct.induct()

    Eq << algebra.suffice.imply.cond.induct.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

