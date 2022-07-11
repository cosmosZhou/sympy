from util import *


@apply
def apply(M_is_positive, lt, x=None):
    M = M_is_positive.of(Expr > 0)
    U, m2 = lt.of(Less)
    S[M] = m2.of(Expr ** 2)

    if x is None:
        x = lt.generate_var(real=True)
    return Any[x:Interval(-M, M, left_open=True, right_open=True)](x ** 2 > U)


@prove
def prove(Eq):
    from axiom import algebra, sets

    M, U = Symbol(real=True, given=True)
    Eq << apply(M > 0, U < M ** 2)

    x = Eq[-1].variable
    Eq.is_negative, Eq.is_nonnegative = algebra.cond.given.et.infer.split.apply(Eq[-1], cond=U < 0)

    Eq << algebra.cond.imply.infer.apply(Eq[0], cond=U >= 0)

    Eq << algebra.cond.imply.infer.et.apply(Eq[1], cond=Eq[-1].lhs)

    Eq << Eq[-1].this.rhs.apply(algebra.ge_zero.lt.imply.lt.sqrt)

    Eq << algebra.gt_zero.imply.eq.abs.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq.is_negative.this.rhs.apply(algebra.any.given.cond.subs, x, 0)

    Eq << algebra.infer.given.et.infer.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(sets.el_interval.given.et)

    Eq << algebra.infer.given.cond.apply(Eq[-1])

    Eq << Eq[0].reversed

    Eq << Eq.is_nonnegative.this.rhs.apply(algebra.any.given.cond.subs, x, (sqrt(U) + M) / 2)

    Eq << algebra.infer.given.et.infer.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(algebra.gt.given.gt_zero), Eq[-1].this.rhs.apply(sets.el_interval.given.et)

    Eq <<= Eq[-2].this.find(Add).apply(algebra.add.to.mul.st.square_difference), algebra.infer.given.et.infer.apply(Eq[-1])

    Eq <<= Eq[-3].this.rhs.apply(algebra.mul_gt_zero.given.et.gt_zero), Eq[-2].this.rhs * 2, Eq[-1].this.rhs * 2

    Eq <<= algebra.infer.given.et.infer.apply(Eq[-3]), Eq[-2].this.rhs.apply(algebra.lt.transport, lhs=0), Eq[-1].this.rhs.apply(algebra.gt.given.gt_zero)

    Eq <<= Eq[-3].this.rhs * 2, Eq[-2].this.rhs * 2, Eq[-1].this.rhs.apply(algebra.add_gt_zero.given.et, index=0)

    Eq <<= Eq[-3].this.rhs.apply(algebra.add_gt_zero.given.et, index=0), Eq[-2].this.rhs.apply(algebra.gt.transport), algebra.infer.given.et.infer.apply(Eq[-1])

    Eq <<= algebra.infer.given.et.infer.apply(Eq[-4]), Eq[-3].this.rhs.reversed, Eq[-2].this.rhs / 3, Eq[-1].this.lhs.apply(algebra.ge_zero.imply.sqrt_ge_zero)

    Eq << Eq[-1].this.rhs / 3


if __name__ == '__main__':
    run()
# created on 2019-08-26
