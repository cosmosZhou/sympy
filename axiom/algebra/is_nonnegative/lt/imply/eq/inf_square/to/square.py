from util import *


@apply
def apply(is_nonnegative, lt, left_open=True, right_open=True, x=None):
    _m = is_nonnegative.of(Expr >= 0)
    m, M = lt.of(Less)
    assert m == _m
    if x is None:
        x = lt.generate_var(real=True)

    self = Inf[x:Interval(m, M, left_open=left_open, right_open=right_open)](x ** 2)
    return Equal(self, m ** 2)


@prove
def prove(Eq):
    from axiom import sets, algebra

    m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(m >= 0, m < M, x=x)

    Eq << sets.lt.imply.el.interval.average.apply(Eq[1])

    Eq << sets.el.imply.et.split.interval.apply(Eq[-1])

    Eq << algebra.gt.ge.imply.gt.transit.apply(Eq[-2], Eq[0])

    Eq.eq_max = algebra.is_nonnegative.lt.imply.eq.max.apply(Eq[0], Eq[1])

    Eq << algebra.ge.lt.imply.gt.transit.apply(Eq[0], Eq[1])

    Eq.eq_abs_M = algebra.is_positive.imply.eq.abs.apply(Eq[-1])

    Eq.eq_abs_m = algebra.is_nonnegative.imply.eq.abs.apply(Eq[0])

    Eq << algebra.eq.given.et.squeeze.apply(Eq[2])

    y = Symbol(real=True)
    Eq <<= algebra.le_inf.given.all_any_lt.apply(Eq[-2], y), algebra.ge_inf.given.all_ge.apply(Eq[-1])

    Eq <<= algebra.all.given.et.all.split.apply(Eq[-2], cond=y <= M ** 2), algebra.all.given.suffice.apply(Eq[-1])

    Eq <<= algebra.all.given.suffice.apply(Eq[-2]), Eq[-3].subs(Eq.eq_max), Eq[-1].this.lhs.apply(sets.el.imply.gt.split.interval)

    Eq <<= Eq[-3].this.rhs.apply(algebra.any.given.cond.subs, x, (m + sqrt(y)) / 2), Eq[-2].this.expr.apply(algebra.any.given.cond.subs, x, (M + m) / 2), Eq[-1].this.lhs.apply(algebra.cond.imply.suffice.et, cond=Eq[0])

    Eq <<= algebra.suffice.given.et.suffice.apply(Eq[-3]), algebra.et.given.et.apply(Eq[-2]), algebra.suffice.given.et.suffice.st.suffice.apply(Eq[-1])

    Eq << Eq[-2].this.apply(algebra.cond.given.cond.subs.bool, cond=Eq[0], invert=True)

    Eq <<= Eq[-5].this.lhs.apply(sets.el.imply.gt.split.interval), Eq[-4].this.rhs.apply(sets.el.given.el.sub, m / 2), Eq[-3].this.expr.apply(algebra.lt.given.is_positive), Eq[-1].this.lhs.apply(algebra.is_nonnegative.gt.imply.gt.square)

    Eq << Eq[-1].this.lhs.apply(algebra.gt.imply.ge.relax)

    Eq <<= Eq[-4].this.rhs.apply(algebra.lt.given.is_positive), Eq[-3].this.rhs.apply(sets.el.given.el.mul.interval, 2), algebra.all.given.suffice.apply(Eq[-2])

    Eq <<= Eq[-3].this.rhs.lhs.apply(algebra.add.to.mul.st.square_difference), Eq[-2].this.lhs.apply(sets.el.imply.el.sqrt), Eq[-1].this.rhs.lhs.apply(algebra.add.to.mul.st.square_difference)

    Eq <<= Eq[-3].this.rhs.apply(algebra.mul_is_positive.given.et.is_positive), Eq[-2].subs(Eq.eq_abs_m, Eq.eq_abs_M), Eq[-1].this.rhs.apply(algebra.mul_is_positive.given.et.is_positive)

    Eq <<= algebra.suffice.given.et.suffice.apply(Eq[-3]), Eq[-2].this.rhs.apply(sets.el.given.et.strengthen, M, strict=True), algebra.suffice.given.et.suffice.apply(Eq[-1])

    Eq <<= Eq[-5].this.rhs * 2, Eq[-4].this.rhs * 2, algebra.suffice.given.cond.apply(Eq[-3]), Eq[-2].this.lhs.apply(algebra.gt.imply.gt.sqrt), Eq[-1].this.rhs.apply(algebra.add_is_positive.given.et.is_positive)

    Eq << Eq[-3] + (m - M)

    Eq <<= Eq[-5].this.lhs.apply(algebra.gt.imply.gt.sqrt), Eq[-4].this.rhs.apply(algebra.add_is_positive.given.et), Eq[-2].subs(Eq.eq_abs_M), algebra.suffice.given.et.suffice.apply(Eq[-1])

    Eq <<= Eq[-5].subs(Eq.eq_abs_m), Eq[-4].this.lhs.apply(algebra.gt.imply.gt.relax, lower=0), Eq[-3].this.rhs.apply(algebra.gt.transposition, lhs=slice(0, 2)), algebra.suffice.given.cond.apply(Eq[-2]), Eq[-1].this.lhs.apply(algebra.gt.imply.gt.relax, lower=0)

    Eq << Eq[-4].this.lhs.apply(algebra.gt.imply.is_positive)

    Eq << Eq[-1].this.lhs.apply(algebra.is_positive.imply.sqrt_is_positive)

    Eq <<= algebra.suffice.given.et.suffice.apply(Eq[-3]), Eq[-2].this.rhs.apply(algebra.gt.given.et.strengthen, M, strict=True)

    Eq <<= algebra.suffice.given.cond.apply(Eq[-2]), Eq[-3].this.rhs / 3, Eq[-1].this.lhs.apply(algebra.gt.imply.ge.relax)

    Eq << algebra.suffice.given.cond.apply(Eq[-1])

    Eq << Eq[-1] * 2 - M

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()