from util import *


@apply
def apply(lt, k=None):
    a, b = lt.of(Less)
    assert a.is_integer and b.is_integer
    if k is None:
        k = lt.generate_var(integer=True)
    return Equal(Cup[k:a:b](Interval(k, k + 1, right_open=True)), Interval(a, b, right_open=True))


@prove
def prove(Eq):
    from axiom import algebra, sets

    a, b, k = Symbol(integer=True)
    Eq << apply(a < b, k)

    Eq << algebra.cond.given.et.infer.split.apply(Eq[1], cond=a >= 0)

    Eq <<= algebra.cond.imply.infer.et.apply(Eq[0], cond=Eq[-2].lhs), algebra.cond.imply.infer.et.apply(Eq[0], cond=Eq[-1].lhs)

    Eq <<= Eq[-2].this.rhs.apply(sets.ge_zero.lt.imply.eq.cup.to.interval.right_open), Eq[-1].this.rhs.apply(sets.lt_zero.lt.imply.eq.cup.to.interval.right_open)


if __name__ == '__main__':
    run()
# created on 2021-02-22
