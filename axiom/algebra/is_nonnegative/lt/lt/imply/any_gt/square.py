from util import *


@apply
def apply(m_is_nonnegative, lt_mM, lt, x=None):
    _m = m_is_nonnegative.of(Expr >= 0)
    m, M = lt_mM.of(Less)
    assert m == _m

    U, M2 = lt.of(Less)
    _M = M2.of(Expr ** 2)
    assert _M == M or _M == -M
    if x is None:
        x = lt.generate_var(real=True)
    return Any[x:Interval(m, M, left_open=True, right_open=True)](x ** 2 > U)


@prove
def prove(Eq):
    from axiom import algebra, sets

    m, M, U = Symbol(real=True, given=True)
    Eq << apply(m >= 0, m < M, U < M ** 2)

    x = Eq[-1].variable
    Eq.ge, Eq.lt = algebra.cond.given.et.suffice.split.apply(Eq[-1], cond=U >= m ** 2)

    Eq << algebra.lt.ge.imply.gt.transit.apply(Eq[1], Eq[0])

    Eq << Eq.lt.this.rhs.apply(algebra.any.given.cond.subs, x, (m + M) / 2)

    Eq.gt, Eq.contains = algebra.suffice.given.et.suffice.apply(Eq[-1])

    Eq << Eq[1].reversed + m

    Eq << Eq[-1] / 2

    Eq << algebra.is_nonnegative.gt.imply.gt.square.apply(Eq[0], Eq[-1])

    Eq << algebra.cond.imply.suffice.et.apply(Eq[-1], cond=U < m ** 2)

    Eq << Eq[-1].this.rhs.apply(algebra.gt.lt.imply.gt.transit)

    Eq << algebra.suffice.given.cond.apply(Eq.contains)

    Eq << sets.lt.imply.el.interval.average.apply(Eq[1])

    Eq << Eq.ge.this.rhs.apply(algebra.any.given.cond.subs, x, (sqrt(U) + M) / 2)

    Eq << Eq[-1].this.find(Element).apply(sets.el.given.et.split.interval)

    Eq << algebra.suffice.given.et.suffice.apply(Eq[-1], index=None)

    Eq <<= Eq[-3].this.rhs.apply(algebra.gt.given.is_positive), Eq[-2].this.rhs.apply(algebra.lt.transposition, lhs=0)

    Eq <<= Eq[-2].this.find(Add).apply(algebra.add.to.mul.st.square_difference), Eq[-1].this.rhs * 2

    Eq <<= Eq[-2].this.lhs.apply(algebra.ge.imply.ge.relax, lower=0), Eq[-1].this.lhs.apply(algebra.ge.imply.ge.relax, lower=0)

    Eq.is_nonnegative = Eq[-2].this.rhs.apply(algebra.mul_is_positive.given.et.is_positive)

    Eq <<= algebra.cond.imply.suffice.et.apply(Eq[2], cond=U >= 0)

    Eq << Eq[-1].this.rhs.apply(algebra.is_nonnegative.lt.imply.lt.sqrt)

    Eq << algebra.is_positive.imply.eq.abs.apply(Eq[4])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << algebra.suffice.given.et.suffice.apply(Eq.is_nonnegative)

    Eq <<= Eq[-2].this.rhs * 2, Eq[-1].this.rhs * 2

    Eq <<= Eq[-2].this.rhs.apply(algebra.add_is_positive.given.et, 0), Eq[-1].this.rhs.apply(algebra.is_positive.given.gt)

    Eq <<= Eq[-2].this.rhs.args[0] / 3, Eq[-1].this.rhs.reversed

    Eq <<= algebra.suffice.given.et.suffice.apply(Eq[-1])

    Eq <<= algebra.suffice.given.cond.apply(Eq[-2])

    Eq <<= Eq[-1].this.lhs.apply(algebra.is_nonnegative.imply.sqrt_is_nonnegative)

    Eq << algebra.cond.imply.suffice.et.apply(Eq[1].reversed, cond=U >= m ** 2)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.ge.imply.ge.sqrt)

    Eq << algebra.is_nonnegative.imply.eq.abs.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.gt.ge.imply.gt.add)

    Eq << Eq[-1].this.rhs / 2


if __name__ == '__main__':
    run()