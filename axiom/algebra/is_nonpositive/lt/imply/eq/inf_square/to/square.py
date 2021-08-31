from util import *


@apply
def apply(is_nonpositive, lt, left_open=True, right_open=True, x=None):
    _M = is_nonpositive.of(Expr <= 0)
    m, M = lt.of(Less)
    assert M == _M
    if x is None:
        x = lt.generate_var(real=True)
    
    self = Inf[x:Interval(m, M, left_open=left_open, right_open=right_open)](x ** 2)    
    return Equal(self, M ** 2)


@prove
def prove(Eq):
    from axiom import algebra, sets

    m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(M <= 0, m < M, x=x)

    Eq << algebra.is_nonpositive.lt.imply.eq.max.apply(Eq[0], Eq[1])

    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[0], Eq[1])

    Eq << algebra.eq.given.et.squeeze.apply(Eq[2])

    y = Symbol(real=True)
    Eq <<= algebra.le_inf.given.all_any_lt.apply(Eq[-2], y), algebra.ge_inf.given.all_le.apply(Eq[-1])

    Eq <<= algebra.all.given.et.all.split.apply(Eq[-2], cond=y <= m ** 2), algebra.all.given.suffice.apply(Eq[-1])

    Eq <<= algebra.all.given.suffice.apply(Eq[-3]), Eq[-2].subs(Eq[3]), Eq[-1].this.lhs.apply(sets.el.imply.lt.split.interval)

    Eq <<= Eq[-2].this.expr.apply(algebra.any.given.cond.subs, x, (M + m) / 2), Eq[-1].this.lhs.apply(algebra.cond.imply.suffice.et, cond=Eq[0])

    Eq << algebra.suffice.given.et.suffice.st.suffice.apply(Eq[-1])

    Eq << Eq[-2].this.apply(algebra.cond.given.cond.subs.bool, given=Eq[0], invert=True)

    Eq <<= Eq[-1].this.lhs.apply(algebra.is_nonpositive.lt.imply.lt.square)

    Eq <<= Eq[-1].this.lhs.apply(algebra.lt.imply.ge.relax)


if __name__ == '__main__':
    run()