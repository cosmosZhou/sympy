from util import *


@apply
def apply(lt, lt_max, x=None):
    U, maxi = lt_max.of(Less)
    _M, _m = maxi.of(Max[Expr ** 2, Expr ** 2])
    if x is None:
        x = lt.generate_var(real=True)
    m, M = lt.of(Less)
    assert {M, m} == {_M, _m}
    return Any[x:Interval(m, M, left_open=True, right_open=True)](x ** 2 > U)


@prove
def prove(Eq):
    from axiom import algebra

    m, M, U = Symbol(real=True, given=True)
    Eq << apply(m < M, U < Max(M ** 2, m ** 2))

    Eq << algebra.cond.given.et.infer.split.apply(Eq[-1], cond=M > 0)

    Eq <<= algebra.cond.given.et.infer.split.apply(Eq[-2], cond=m > 0), algebra.cond.given.et.infer.split.apply(Eq[-1], cond=m > 0)

    Eq <<= Eq[-4].this.apply(algebra.infer.flatten), Eq[-3].this.apply(algebra.infer.flatten), Eq[-2].this.apply(algebra.infer.flatten), Eq[-1].this.apply(algebra.infer.flatten)

    Eq <<= algebra.cond.imply.infer.et.apply(Eq[0] & Eq[1], cond=Eq[-4].lhs),\
        algebra.cond.imply.infer.et.apply(Eq[0] & Eq[1], cond=Eq[-3].lhs),\
        Eq[-2].this.lhs.apply(algebra.le.gt.imply.lt.transit),\
        algebra.cond.imply.infer.et.apply(Eq[0] & Eq[1], cond=Eq[-1].lhs)

    Eq <<= Eq[-3].this.rhs.apply(algebra.cond.imply.et.infer.et.split, cond=M + m > 0), \
        Eq[-1].this.rhs.args[::2].apply(algebra.le_zero.lt.imply.eq.max, simplify=None, ret=slice(None)), \
        Eq[-4].this.rhs.args[-1].apply(algebra.gt.imply.ge.relax), \
        Eq[-2].this.lhs.apply(algebra.lt.imply.le.relax)

    Eq <<= algebra.infer.imply.et.infer.apply(Eq[-4], simplify=None), \
        Eq[-3].this.rhs.args[1:3].apply(algebra.eq.cond.imply.cond.subs, simplify=None), \
        Eq[-2].this.rhs.args[1:].apply(algebra.ge_zero.lt.imply.eq.max, ret=slice(None)), \
        Eq[-1].this.apply(algebra.infer.contraposition)

    Eq <<= Eq[-5].this.rhs.rhs.apply(algebra.et.imply.cond, index=slice(None, None, 2), simplify=None), \
        Eq[-4].this.rhs.rhs.apply(algebra.et.imply.cond, index=slice(None, 3), simplify=None), \
        Eq[-3].this.rhs.args[:3].apply(algebra.le_zero.lt.lt.imply.any_gt.square), \
        Eq[-2].this.rhs.args[:2].apply(algebra.eq.cond.imply.cond.subs), \
        algebra.infer.given.cond.apply(Eq[-1]).reversed

    Eq <<= Eq[-3].this.rhs.rhs.args[0].apply(algebra.gt.transport, lhs=0), \
        Eq[-2].this.rhs.rhs.args[0].apply(algebra.le.transport), \
        Eq[-1].this.rhs.apply(algebra.ge_zero.lt.lt.imply.any_gt.square)

    Eq <<= Eq[-2].this.rhs.rhs.args[1:].apply(algebra.le_zero.gt.imply.eq.max, ret=1), \
        Eq[-1].this.rhs.rhs.args[:2].apply(algebra.gt_zero.le.imply.eq.max, ret=0)

    Eq <<= Eq[-2].this.rhs.rhs.args[:2].apply(algebra.eq.cond.imply.cond.subs), \
        Eq[-1].this.rhs.rhs.args[1:].apply(algebra.eq.cond.imply.cond.subs)

    Eq <<= Eq[-2].this.rhs.apply(algebra.infer.imply.infer.et), \
        Eq[-1].this.rhs.rhs.args[0].apply(algebra.gt.imply.ge.relax)

    Eq.is_positive, Eq.is_nonpositive = Eq[-2].this.rhs.rhs.apply(algebra.le_zero.gt_zero.lt.imply.any_gt.square),\
        Eq[-1].this.rhs.apply(algebra.infer.imply.infer.et)

    Eq <<= Eq.is_nonpositive.this.rhs.rhs.apply(algebra.cond.imply.et.infer.split, cond=m + M < 0)

    Eq << Eq[-1].this.rhs.apply(algebra.infer.imply.et.infer)

    Eq << algebra.infer.imply.et.infer.apply(Eq[-1], simplify=None)

    Eq <<= Eq[-2].this.rhs.rhs.apply(algebra.et.imply.cond, index=slice(1, 3)), Eq[-1].this.rhs.rhs.apply(algebra.et.imply.cond, index=2)

    Eq <<= Eq[-2].this.rhs.apply(algebra.infer.imply.infer.et), Eq[-1].this.rhs.apply(algebra.infer.imply.infer.et)

    Eq.is_negative = Eq[-2].this.rhs.rhs.apply(algebra.ge_zero.lt_zero.lt.imply.any_gt.square)

    Eq << Eq[-1].this.rhs.rhs.args[0].apply(algebra.eq.transport, lhs=0)

    Eq << Eq[-1].this.rhs.rhs.apply(algebra.eq.cond.imply.cond.subs, ret=1)

    Eq << algebra.infer.imply.infer.et.apply(Eq[-1], index=0)

    Eq << Eq[-1].this.rhs.apply(algebra.cond.infer.imply.infer.et.rhs)

    Eq << Eq[-1].this.rhs.rhs.args[:2].apply(algebra.gt_zero.lt.imply.any_gt.square)

    Eq << Eq[-1].this.rhs.rhs.apply(algebra.eq.cond.imply.cond.subs, reverse=True)

    Eq <<= Eq[-1] & Eq.is_negative & Eq.is_positive


if __name__ == '__main__':
    run()
# created on 2019-09-08
