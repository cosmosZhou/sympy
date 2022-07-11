from util import *


@apply
def apply(lt, x=None, left_open=True, right_open=True):
    m, M = lt.of(Less)
    return Equal(Inf[x:Interval(m, M, left_open=left_open, right_open=right_open)](x), m)


@prove
def prove(Eq):
    from axiom import algebra, sets

    m, M, a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(m < M, x)

    Eq.eq_max = algebra.lt.imply.eq.max.apply(Eq[0])

    Eq << algebra.eq.given.et.squeeze.apply(Eq[-1])

    y = Symbol(real=True)
    Eq <<= algebra.inf_le.given.all_any_lt.apply(Eq[-2], y), algebra.inf_ge.given.all_ge.apply(Eq[-1])

    Eq <<= algebra.all.given.et.all.split.apply(Eq[-2], cond=y <= M), algebra.all.given.ou.apply(Eq[-1])

    Eq <<= Eq[-3].subs(Eq.eq_max), Eq[-2].this.expr.apply(algebra.any.given.cond.subs, x, (m + y) / 2), Eq[-1].this.args[0].apply(sets.notin_interval.given.ou)

    Eq <<= Eq[-2].this.expr.apply(algebra.any.given.cond.subs, x, (m + M) / 2), algebra.all_et.given.et.all.apply(Eq[-1])

    Eq <<= algebra.et.given.et.apply(Eq[-3]), algebra.all.given.infer.apply(Eq[-2]), algebra.all.given.infer.apply(Eq[-1])

    Eq << sets.lt.imply.el.interval.average.apply(Eq[0])

    Eq <<= algebra.all.given.infer.apply(Eq[-3]), Eq[-2].this.rhs * 2, Eq[-1].this.rhs.apply(sets.el.given.el.mul.interval, 2)

    Eq <<= algebra.infer.given.et.infer_et.apply(Eq[-3], cond=Eq[0]), Eq[-2].this.rhs - y, Eq[-1].this.rhs.apply(sets.el.given.el.sub, m)

    Eq << Eq[-2].this.lhs.apply(sets.el_interval.imply.gt)

    Eq <<= Eq[-3].this.lhs.apply(algebra.lt.gt.imply.gt.transit, ret=1), Eq[-1].this.rhs.apply(sets.el.given.et.strengthen, lower=M, strict=True)

    Eq <<= Eq[-2].this.lhs.apply(algebra.gt.gt.imply.gt.add), algebra.infer.given.cond.apply(Eq[-1])

    Eq << Eq[-1] + (m - M)

    Eq << Eq[-2].this.rhs * 2


if __name__ == '__main__':
    run()
# created on 2019-08-27
