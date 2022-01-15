from util import *


@apply
def apply(lt, left_open=True, right_open=True, x=None):
    m, M = lt.of(Less)
    if x is None:
        x = lt.generate_var(real=True)

    self = Inf[x:Interval(m, M, left_open=left_open, right_open=right_open)](x ** 2)
    return Equal(self, Piecewise((0, (m <= 0) & (M >= 0)), (Min(m ** 2, M ** 2), True)))


@prove
def prove(Eq):
    from axiom import algebra

    m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(m < M, x=x)

    Eq <<= algebra.cond.imply.infer.et.apply(Eq[0], cond=m >= 0), algebra.cond.imply.infer.et.apply(Eq[0], cond=M <= 0)

    Eq <<= Eq[-2].this.rhs.apply(algebra.ge_zero.lt.imply.eq.inf_square.to.square), Eq[-2].this.rhs.apply(algebra.ge_zero.lt.imply.eq.min), \
        Eq[-1].this.rhs.apply(algebra.le_zero.lt.imply.eq.inf_square.to.square), Eq[-1].this.rhs.apply(algebra.le_zero.lt.imply.eq.min)

    Eq <<= Eq[-3] & Eq[-4], Eq[-1] & Eq[-2]

    Eq <<= Eq[-2].this.rhs.apply(algebra.eq.eq.imply.eq.subs, swap=True, reverse=True), Eq[-1].this.rhs.apply(algebra.eq.eq.imply.eq.subs, swap=True, reverse=True)

    Eq << algebra.cond.given.et.infer.split.apply(Eq[1], cond=M >= 0)

    Eq <<= algebra.infer.given.infer.subs.bool.apply(Eq[-2]), algebra.infer.given.infer.subs.bool.apply(Eq[-1], invert=True)

    Eq <<= Eq[-1].this.lhs.apply(algebra.lt_zero.imply.le_zero), algebra.cond.given.et.infer.split.apply(Eq[-2], cond=m <= 0)

    Eq <<= algebra.infer.given.infer.subs.bool.apply(Eq[-2]), algebra.infer.given.infer.subs.bool.apply(Eq[-1], invert=True)

    Eq <<= Eq[-2].this.apply(algebra.infer.flatten), Eq[-1].this.apply(algebra.infer.flatten)

    Eq <<= algebra.cond.given.et.infer.split.apply(Eq[-2], cond=M > 0), algebra.infer_et.given.infer.delete.apply(Eq[-1], 0)

    Eq <<= Eq[-3].this.apply(algebra.infer.flatten), Eq[-2].this.apply(algebra.infer.flatten), Eq[-1].this.lhs.apply(algebra.gt.imply.ge.relax)

    Eq <<= Eq[-2].this.lhs.apply(algebra.gt_zero.le_zero.imply.eq.inf_square.to.zero), algebra.infer_et.given.infer.subs.apply(Eq[-1])

    Eq << algebra.infer_et.given.infer.delete.apply(Eq[-1])

    Eq <<= algebra.infer.given.et.infer_et.apply(Eq[-1], cond=Eq[0])

    Eq <<= Eq[-1].this.lhs.apply(algebra.eq.cond.imply.cond.subs)

    Eq << Eq[-1].this.lhs.apply(algebra.lt_zero.imply.eq.inf_square.to.zero, x)


if __name__ == '__main__':
    run()
# created on 2019-12-21
