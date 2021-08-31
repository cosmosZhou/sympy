from util import *


@apply
def apply(le, _le, right_open=True, left_open=None):
    x, a = le.of(LessEqual)
    b, _x = _le.of(LessEqual)
    if x != _x:
        a, x, _x, b = _x, b, a, x,
    assert x == _x
    if left_open is not None:
        right_open = not left_open
    return Equal(Interval(b, x, right_open=right_open) | Interval(x, a, left_open=not right_open), Interval(b, a))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, x = Symbol(real=True, given=True)
    Eq << apply(x <= b, a <= x)

    Eq << sets.eq.given.et.suffice.apply(Eq[2])

    Eq <<= Eq[-2].this.lhs.apply(sets.el.imply.ou.split.union), Eq[-1].this.rhs.apply(sets.el.given.ou.split.union)

    Eq <<= algebra.suffice.given.et.suffice.split.ou.apply(Eq[-2]), Eq[-1].this.apply(algebra.suffice.contraposition)

    Eq <<= Eq[-3].this.lhs.apply(sets.el.imply.et.split.interval), Eq[-2].this.lhs.apply(sets.el.imply.et.split.interval), Eq[-1].this.lhs.args[0].apply(sets.notin.imply.ou.split.interval)

    Eq <<= Eq[-3].this.rhs.apply(sets.el.given.et.split.interval), Eq[-2].this.rhs.apply(sets.el.given.et.split.interval), Eq[-1].this.lhs.args[1].apply(sets.notin.imply.ou.split.interval)

    Eq <<= algebra.cond.imply.suffice.et.apply(Eq[0], cond=Eq[-3].lhs), algebra.cond.imply.suffice.et.apply(Eq[1], cond=Eq[-2].lhs), Eq[-1].this.rhs.apply(sets.notin.given.ou.split.interval)

    Eq <<= Eq[-3].this.rhs.args[:2].apply(algebra.le.lt.imply.le.relax), Eq[-2].this.rhs.args[::2].apply(algebra.le.ge.imply.ge.transit),  Eq[-1].this.lhs.apply(algebra.et.imply.ou)

    Eq << algebra.suffice.given.et.suffice.split.ou.apply(Eq[-1])

    Eq << algebra.suffice.given.suffice.split.et.apply(Eq[-2], 1)

    Eq << algebra.suffice.given.suffice.split.et.apply(Eq[-1])


if __name__ == '__main__':
    run()