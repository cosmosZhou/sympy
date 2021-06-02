from util import *


@apply
def apply(n):
    k = Symbol.k(integer=True)
    return Equal(Limit[n:oo](Sum[k:1:n](1 / k) / log(n + 1)), 1)


@prove
def prove(Eq):
    from axiom import calculus, sets, algebra
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)

    x = Symbol.x(real=True)
    x0 = Symbol.x0(real=True, positive=True)
    Eq.is_continuous = Equal(Limit[x:x0](1 / x), 1 / x0, plausible=True)

    Eq << Eq.is_continuous.this.lhs.doit()

    k, *ab = Eq[-1].lhs.args[0].args[-1].limits[0]
    k = k.copy(domain=Range(*ab))

    Eq << Eq.is_continuous.apply(algebra.cond.imply.all.restrict, (x0, k, k + 1))

    Eq.mean_value_theorem = calculus.integral.mean_value_theorem.apply(Eq[-1])

    Eq << algebra.imply.all.limits_assert.apply(Eq[-1].limits)

    Eq << Eq[-1].inverse()

    Eq << Eq[-1].this.function.apply(sets.contains.imply.et.split.interval)

    Eq << algebra.all_et.imply.all.apply(Eq[-1])

    Eq <<= algebra.all.any.imply.any_et.apply(Eq[-2], Eq.mean_value_theorem), \
    algebra.all.any.imply.any_et.apply(Eq[-1], Eq.mean_value_theorem)

    Eq <<= Eq[-2].this.function.apply(algebra.eq.cond.imply.cond.subs, reverse=True), \
    Eq[-1].this.function.apply(algebra.eq.cond.imply.cond.subs, reverse=True)

    Eq <<= Eq[-2].apply(algebra.cond.imply.all.restrict, (k, 1, n)), Eq[-1].apply(algebra.cond.imply.all.restrict, (k, 1, n - 1))

    Eq <<= algebra.all_le.imply.le.sum.apply(Eq[-2]), algebra.all_ge.imply.ge.sum.apply(Eq[-1])

    Eq <<= Eq[-2].this.lhs.doit(), Eq[-1].this.lhs.doit().reversed

    k = Eq[-1].lhs.variable
    Eq << Eq[-1].this.lhs.limits_subs(k, k - 1) + 1

    Eq <<= Eq[-3] / Eq[-3].lhs, Eq[-1] / Eq[-3].lhs

    Eq <<= calculus.le.imply.le.limit.apply(Eq[-2], (n, oo)), calculus.le.imply.le.limit.apply(Eq[-1], (n, oo))

    Eq << Eq[-1].this.rhs.doit()

    Eq <<= Eq[-1] & Eq[-3]


if __name__ == '__main__':
    run()

