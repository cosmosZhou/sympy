from util import *


@apply
def apply(lt, le, right_open=False, left_open=False):
    a, x = lt.of(Less)
    _x, b = le.of(LessEqual)
    assert x == _x
    return Equal(Interval(a, x, left_open=left_open, right_open=True) | Interval(x, b, right_open=right_open), Interval(a, b, left_open=left_open, right_open=right_open))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, x = Symbol(real=True, given=True)
    Eq << apply(a < x, x <= b, left_open=True)

    Eq << sets.eq.given.et.infer.apply(Eq[2])

    Eq <<= Eq[-2].this.lhs.apply(sets.el_union.imply.ou), Eq[-1].this.rhs.apply(sets.el_union.given.ou)

    Eq <<= algebra.infer.given.et.infer.split.ou.apply(Eq[-2]), Eq[-1].this.apply(algebra.infer.contraposition)

    Eq <<= Eq[-3].this.lhs.apply(sets.el_interval.imply.et), Eq[-2].this.lhs.apply(sets.el_interval.imply.et), Eq[-1].this.lhs.args[0].apply(sets.notin_interval.imply.ou)

    Eq <<= Eq[-3].this.rhs.apply(sets.el_interval.given.et), Eq[-2].this.rhs.apply(sets.el_interval.given.et), Eq[-1].this.lhs.args[1].apply(sets.notin_interval.imply.ou)

    Eq <<= algebra.cond.imply.infer.et.apply(Eq[1], cond=Eq[-3].lhs), algebra.cond.imply.infer.et.apply(Eq[0], cond=Eq[-2].lhs), Eq[-1].this.rhs.apply(sets.notin_interval.given.ou)

    Eq <<= Eq[-3].this.rhs.args[:2].apply(algebra.le.lt.imply.le.relax), Eq[-2].this.rhs.args[::2].apply(algebra.lt.ge.imply.gt.transit),  Eq[-1].this.lhs.apply(algebra.et.imply.ou)

    Eq << algebra.infer.given.et.infer.split.ou.apply(Eq[-1])

    Eq << algebra.infer.given.infer.split.et.apply(Eq[-2], 1)

    Eq << algebra.infer.given.infer.split.et.apply(Eq[-1], 1)


if __name__ == '__main__':
    run()
# created on 2021-02-20
