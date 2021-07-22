from util import *


@apply
def apply(given):
    (yk, xy_historic), (_yk, y_k_1) = given.of(Equal[Conditioned, Conditioned])

    assert yk == _yk
    y, k = yk.args
    assert y_k_1 == y[k - 1].as_boolean()

    x_historic, y_historic = xy_historic.args
    if y[:k].as_boolean() != y_historic:
        x_historic, y_historic = y_historic, x_historic
    assert y[:k].as_boolean() == y_historic

    return Equal(y[k] | y_historic, y[k] | y[k - 1])


@prove
def prove(Eq):
    from axiom import stats, algebra
    d = Symbol.d(domain=Range(2, oo))
    n = Symbol.n(domain=Range(2, oo))
    x = Symbol.x(shape=(n, d), real=True, random=True, given=True)
    y = Symbol.y(shape=(n,), domain=Range(0, d), random=True, given=True)

    k = Symbol.k(integer=True)

    Eq << apply(Equal(y[k] | (x[:k].as_boolean() & y[:k].as_boolean()), y[k] | y[k - 1]))

    Eq << Eq[0].apply(algebra.cond.imply.all.restrict, (k, 2, oo))

    Eq << Eq[-1].this().expr.lhs.rhs.args[1].apply(algebra.eq.imply.et.split.blockmatrix, slice(-1))

    Eq << stats.eq.imply.eq.single_condition_w.apply(Eq[-1], wrt=Eq[-1].lhs.rhs.args[1].lhs)

    Eq << Eq[1].apply(algebra.cond.given.et.all, cond=k >= 2)

    Eq << Eq[-1].this().expr.lhs.rhs.apply(algebra.eq.given.et.split.blockmatrix, slice(-1))


if __name__ == '__main__':
    run()
