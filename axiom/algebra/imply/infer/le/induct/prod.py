from util import *


@apply(given=None)
def apply(given, limit):
    xk, yk = given.of(LessEqual)
    k, a, b = limit
    assert xk._has(k)
    assert yk._has(k)
    assert xk >= 0

    return Infer(All[k:a:b](xk <= yk), Product[k:a:b](xk) <= Product[k:a:b](yk))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True, given=False)
    k = Symbol(integer=True)
    y = Symbol(shape=(oo,), integer=True)
    x = Symbol(shape=(oo,), integer=True, nonnegative=True)
    Eq << apply(x[k] <= y[k], (k, 0, n))

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << algebra.infer.imply.infer.et.both_sided.apply(Eq[0], cond=x[n] <= y[n])

    Eq << Eq[-1].this.lhs.apply(algebra.cond.all.given.all.push_back)

    Eq << Eq[-1].this.rhs.apply(algebra.le.le.imply.le.prod.push_back)

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.infer.imply.cond.induct.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

# created on 2019-09-27
