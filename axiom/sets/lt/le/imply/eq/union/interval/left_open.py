from util import *


@apply
def apply(lt, le, right_open=False, left_open=False):
    a, x = lt.of(Less)
    _x, b = le.of(LessEqual)
    assert x == _x
    return Equal(Interval(a, x, left_open=left_open) | Interval(x, b, left_open=True, right_open=right_open), Interval(a, b, left_open=left_open, right_open=right_open))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, x = Symbol(real=True, given=True)
    Eq << apply(a < x, x <= b)

    Eq << sets.eq.given.et.suffice.apply(Eq[2])

    Eq <<= Eq[-2].this.lhs.apply(sets.el.imply.ou.split.union), Eq[-1].this.rhs.apply(sets.el.given.ou.split.union)

    Eq <<= algebra.suffice.given.et.suffice.split.ou.apply(Eq[-2]), Eq[-1].this.apply(algebra.suffice.contraposition)

    Eq <<= Eq[-3].this.lhs.apply(sets.el.imply.et.split.interval), Eq[-2].this.lhs.apply(sets.el.imply.et.split.interval), Eq[-1].this.lhs.args[0].apply(sets.notin.imply.ou.split.interval)

    Eq <<= Eq[-3].this.rhs.apply(sets.el.given.et.split.interval), Eq[-2].this.rhs.apply(sets.el.given.et.split.interval), Eq[-1].this.lhs.args[1].apply(sets.notin.imply.ou.split.interval)

    Eq <<= algebra.cond.imply.suffice.et.apply(Eq[0], cond=Eq[-3].lhs), algebra.cond.imply.suffice.et.apply(Eq[1], cond=Eq[-2].lhs), Eq[-1].this.rhs.apply(sets.notin.given.ou.split.interval)

    Eq <<= Eq[-3].this.rhs.args[:2].apply(algebra.lt.gt.imply.ge.relax), Eq[-2].this.rhs.args[:2].apply(algebra.le.le.imply.le.transit),  Eq[-1].this.lhs.apply(algebra.et.imply.ou)

    Eq << algebra.suffice.given.et.suffice.split.ou.apply(Eq[-1])

    Eq << algebra.suffice.given.suffice.split.et.apply(Eq[-2], 1)

    Eq << algebra.suffice.given.suffice.split.et.apply(Eq[-1])


if __name__ == '__main__':
    run()