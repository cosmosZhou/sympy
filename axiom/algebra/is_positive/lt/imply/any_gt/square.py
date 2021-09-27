from util import *


@apply
def apply(M_is_positive, lt, x=None):
    M = M_is_positive.of(Expr > 0)
    U, m2 = lt.of(Less)
    _M = m2.of(Expr ** 2)
    assert _M == M
    if x is None:
        x = lt.generate_var(real=True)
    return Any[x:Interval(-M, M, left_open=True, right_open=True)](x ** 2 > U)


@prove
def prove(Eq):
    from axiom import algebra, sets

    M, U = Symbol(real=True, given=True)
    Eq << apply(M > 0, U < M ** 2)

    x = Eq[-1].variable
    Eq.is_negative, Eq.is_nonnegative = algebra.cond.given.et.suffice.split.apply(Eq[-1], cond=U < 0)

    Eq << algebra.cond.imply.suffice.apply(Eq[0], cond=U >= 0)

    Eq << algebra.cond.imply.suffice.et.apply(Eq[1], cond=Eq[-1].lhs)

    Eq << Eq[-1].this.rhs.apply(algebra.is_nonnegative.lt.imply.lt.sqrt)

    Eq << algebra.is_positive.imply.eq.abs.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq.is_negative.this.rhs.apply(algebra.any.given.cond.subs, x, 0)

    Eq << algebra.suffice.given.et.suffice.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(sets.el.given.et.split.interval)

    Eq << algebra.suffice.given.cond.apply(Eq[-1])

    Eq << Eq[0].reversed

    Eq << Eq.is_nonnegative.this.rhs.apply(algebra.any.given.cond.subs, x, (sqrt(U) + M) / 2)

    Eq << algebra.suffice.given.et.suffice.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(algebra.gt.given.is_positive), Eq[-1].this.rhs.apply(sets.el.given.et.split.interval)

    Eq <<= Eq[-2].this.find(Add).apply(algebra.add.to.mul.st.square_difference), algebra.suffice.given.et.suffice.apply(Eq[-1])

    Eq <<= Eq[-3].this.rhs.apply(algebra.mul_is_positive.given.et.is_positive), Eq[-2].this.rhs * 2, Eq[-1].this.rhs * 2

    Eq <<= algebra.suffice.given.et.suffice.apply(Eq[-3]), Eq[-2].this.rhs.apply(algebra.lt.transposition, lhs=0), Eq[-1].this.rhs.apply(algebra.gt.given.is_positive)

    Eq <<= Eq[-3].this.rhs * 2, Eq[-2].this.rhs * 2, Eq[-1].this.rhs.apply(algebra.add_is_positive.given.et, index=0)

    Eq <<= Eq[-3].this.rhs.apply(algebra.add_is_positive.given.et, index=0), Eq[-2].this.rhs.apply(algebra.gt.transposition), algebra.suffice.given.et.suffice.apply(Eq[-1])

    Eq <<= algebra.suffice.given.et.suffice.apply(Eq[-4]), Eq[-3].this.rhs.reversed, Eq[-2].this.rhs / 3, Eq[-1].this.lhs.apply(algebra.is_nonnegative.imply.sqrt_is_nonnegative)

    Eq << Eq[-1].this.rhs / 3


if __name__ == '__main__':
    run()