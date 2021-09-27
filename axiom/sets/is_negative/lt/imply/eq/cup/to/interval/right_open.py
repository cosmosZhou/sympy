from util import *


@apply
def apply(is_negative, lt, k=None):
    a = is_negative.of(Expr < 0)
    _a, b = lt.of(Less)
    assert _a == a
    assert a.is_integer and b.is_integer
    if k is None:
        k = lt.generate_var(integer=True)
    return Equal(Cup[k:a:b](Interval(k, k + 1, right_open=True)), Interval(a, b, right_open=True))


@prove
def prove(Eq):
    from axiom import algebra, sets

    a, b, k = Symbol(integer=True)
    Eq << apply(a < 0, a < b, k)

    Eq << algebra.cond.given.et.suffice.split.apply(Eq[-1], cond=b >= 0)

    Eq <<= algebra.cond.imply.suffice.et.apply(Eq[0], cond=Eq[-2].lhs), algebra.cond.imply.suffice.et.apply(Eq[0] & Eq[1], cond=Eq[-1].lhs)

    Eq << Eq[-2].this.rhs.apply(sets.is_negative.is_nonnegative.imply.eq.cup.to.interval.right_open)
    Eq << Eq[-1].this.rhs.apply(sets.is_negative.is_negative.lt.imply.eq.cup.to.interval.right_open)


if __name__ == '__main__':
    run()
