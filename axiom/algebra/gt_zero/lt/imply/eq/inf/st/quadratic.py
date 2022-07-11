from util import *


@apply
def apply(gt_zero, lt, fx, x=None, left_open=True, right_open=True):
    from axiom.algebra.le.ge.imply.le.quadratic import quadratic_coefficient
    m, M = lt.of(Less)
    a = gt_zero.of(Expr > 0)

    x, S[a], b, c = quadratic_coefficient(fx, x=x)

    y0 = a * m ** 2 + b * m + c
    y1 = a * M ** 2 + b * M + c
    interval = Interval(m, M, left_open=left_open, right_open=right_open)
    return Equal(Inf[x:interval](fx),
                 Piecewise((c - b ** 2 / (4 * a), Element(-b / (2 * a), interval)),
                           (Min(y0, y1), True)))


@prove
def prove(Eq):
    from axiom import algebra, sets

    m, M, x, a, b, c = Symbol(real=True, given=True)
    Eq << apply(a > 0, m < M, a * x ** 2 + b * x + c, x)

    Eq << algebra.gt_zero.imply.gt_zero.div.apply(Eq[0])

    Eq << Eq[2].this.lhs.apply(algebra.inf.to.add)

    Eq << Eq[-1].this.find(Min).apply(algebra.min.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.to.add)

    Eq << algebra.cond.given.et.infer.split.apply(Eq[-1], cond=Eq[-1].find(Element))

    Eq <<= algebra.infer.given.infer.subs.bool.apply(Eq[-2]), algebra.infer.given.infer.subs.bool.apply(Eq[-1], invert=True)

    Eq <<= algebra.infer.given.et.infer_et.apply(Eq[-2], cond=Eq[0]), Eq[-1].this.lhs.apply(sets.notin_interval.imply.ou)

    Eq <<= Eq[-2].this.lhs.apply(sets.gt_zero.el.imply.eq.inf.st.quadratic, Eq[-2].find(Inf).expr, x), algebra.infer.given.et.infer.split.ou.apply(Eq[-1])

    Eq <<= Eq[-2].this.find(Inf).apply(algebra.inf.limits.subs.offset, Eq[3].lhs * -b /2), Eq[-1].this.find(Inf).apply(algebra.inf.limits.subs.offset, Eq[3].lhs * -b /2)

    Eq <<= Eq[-2].this.find(Inf).expr.expand(), Eq[-1].this.find(Inf).expr.expand()

    Eq <<= Eq[-2].this.find(Equal).apply(algebra.eq.transport, lhs=0), Eq[-1].this.find(Equal).apply(algebra.eq.transport, lhs=0)

    Eq <<= Eq[-2].this.lhs.apply(algebra.le.imply.ge_zero), Eq[-1].this.lhs.apply(algebra.ge.imply.le_zero)

    Eq <<= Eq[-2].this.rhs.rhs.apply(algebra.add.to.min), Eq[-1].this.rhs.rhs.apply(algebra.add.to.min)

    Eq << Eq[1] + Eq[3].lhs * b /2

    Eq <<= algebra.cond.imply.infer.et.apply(Eq[-1] & Eq[0], cond=Eq[-1].lhs >= 0), algebra.cond.imply.infer.et.apply(Eq[-1] & Eq[0], cond=Eq[-1].rhs <= 0)

    Eq <<= Eq[-2].this.rhs.apply(algebra.gt_zero.ge_zero.lt.imply.eq.inf_square.to.square), \
        Eq[-2].this.rhs.apply(algebra.gt_zero.ge_zero.lt.imply.eq.min.to.square),\
        Eq[-1].this.rhs.apply(algebra.gt_zero.le_zero.lt.imply.eq.inf_square.to.square),\
        Eq[-1].this.rhs.apply(algebra.gt_zero.le_zero.lt.imply.eq.min.to.square)

    Eq <<= Eq[-4] & Eq[-3], Eq[-2] & Eq[-1]

    Eq <<= Eq[-2].this.rhs.apply(algebra.eq.eq.imply.eq.transit), Eq[-1].this.rhs.apply(algebra.eq.eq.imply.eq.transit)

    Eq <<= Eq[-2].this.rhs.rhs.expand(), Eq[-1].this.rhs.rhs.expand()





if __name__ == '__main__':
    run()
# created on 2021-10-02
