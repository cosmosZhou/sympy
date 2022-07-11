from util import *


@apply
def apply(n):
    k = Symbol(integer=True)
    return Equal(Limit[n:oo](Sum[k:1:n](1 / k) / log(n + 1)), 1)


@prove
def prove(Eq):
    from axiom import algebra, calculus, sets

    n = Symbol(integer=True, positive=True)
    Eq << apply(n)

    x = Symbol(real=True)
    x0 = Symbol(real=True, positive=True)
    Eq.is_continuous = Equal(Limit[x:x0](1 / x), 1 / x0, plausible=True)

    Eq << Eq.is_continuous.this.lhs.doit()

    k, *ab = Eq[-1].lhs.args[0].args[-1].limits[0]
    k = k.copy(domain=Range(*ab))
    Eq << Eq.is_continuous.apply(algebra.cond.imply.all.restrict, (x0, k, k + 1))

    Eq.mean_value_theorem = calculus.is_continuous.imply.any_eq.mean_value_theorem.apply(Eq[-1])

    Eq << algebra.imply.all.limits_assert.apply(Eq[-1].limits)

    Eq << Eq[-1].this.expr.apply(sets.el.imply.el.inverse.interval)

    Eq << Eq[-1].this.expr.apply(sets.el_interval.imply.et)

    Eq << algebra.all_et.imply.et.all.apply(Eq[-1])

    Eq <<= algebra.all.any.imply.any_et.apply(Eq[-2], Eq.mean_value_theorem), algebra.all.any.imply.any_et.apply(Eq[-1], Eq.mean_value_theorem)

    Eq <<= Eq[-2].this.expr.apply(algebra.eq.cond.imply.cond.subs, reverse=True), \
    Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs, reverse=True)

    Eq <<= Eq[-2].apply(algebra.cond.imply.all.restrict, (k, 1, n)), Eq[-1].apply(algebra.cond.imply.all.restrict, (k, 1, n - 1))

    Eq <<= algebra.all_le.imply.le.sum.apply(Eq[-2]), algebra.all_ge.imply.ge.sum.apply(Eq[-1])

    Eq <<= Eq[-2].this.lhs.doit(), Eq[-1].this.lhs.doit().reversed


    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.subs.offset, -1) + 1

    Eq <<= Eq[-3] / Eq[-3].lhs, Eq[-1] / Eq[-3].lhs

    Eq <<= calculus.le.imply.le.limit.apply(Eq[-2], (n, oo)), calculus.le.imply.le.limit.apply(Eq[-1], (n, oo))

    Eq << Eq[-1].this.rhs.doit()

    Eq <<= Eq[-1] & Eq[-3]


if __name__ == '__main__':
    run()

# created on 2020-06-25
