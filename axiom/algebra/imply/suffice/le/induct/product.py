from util import *


@apply(given=None)
def apply(given, limit):
    xk, yk = given.of(LessEqual)
    k, a, b = limit
    assert xk._has(k)
    assert yk._has(k)
    assert xk >= 0

    return Suffice(All[k:a:b](xk <= yk), Product[k:a:b](xk) <= Product[k:a:b](yk))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol.n(integer=True, positive=True, given=False)
    k = Symbol.k(integer=True)
    y = Symbol.y(shape=(oo,), integer=True)
    x = Symbol.x(shape=(oo,), integer=True, nonnegative=True)
    Eq << apply(x[k] <= y[k], (k, 0, n))

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << algebra.suffice.imply.suffice.et.both_sided.apply(Eq[0], cond=x[n] <= y[n])

    Eq << Eq[-1].this.lhs.apply(algebra.cond.all.given.all.push_back)

    Eq << Eq[-1].this.rhs.apply(algebra.le.le.imply.le.product.push_back)

    Eq << Suffice(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.suffice.imply.cond.induct.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()
