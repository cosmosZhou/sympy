from util import *


@apply
def apply(self):
    interval, k = self.of(Cup[Tuple[0, oo]])
    _k1, _k = interval.of(Interval)
    assert _k1 == -k - 1 and _k == -k
    assert interval.left_open and not interval.right_open

    return Equal(self, Interval(-oo, 0))


@prove
def prove(Eq):
    from axiom import sets, algebra

    k = Symbol(integer=True)
    Eq << apply(Cup[k:oo](Interval(-k - 1, -k, left_open=True)))

    Eq << sets.eq.given.et.suffice.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(sets.el_cup.imply.any_el), Eq[-1].this.rhs.apply(sets.el_cup.given.any_el)

    k = Eq[-1].rhs.variable
    x = Eq[-1].lhs.lhs
    Eq <<= Eq[-2].this.lhs.expr.apply(sets.el.imply.ge.split.interval), Eq[-1].this.rhs.apply(algebra.any.given.cond.subs, k, -Ceiling(x))

    Eq <<= Eq[-2].this.lhs.apply(algebra.any.imply.any_et.limits.unleash, simplify=None), algebra.suffice.given.et.suffice.apply(Eq[-1])

    Eq <<= Eq[-3].this.lhs.expr.args[1].apply(sets.el.imply.ge.split.range), Eq[-2].this.rhs.apply(sets.el.given.et.split.range), algebra.suffice.given.cond.apply(Eq[-1])

    Eq <<= Eq[-3].this.lhs.expr.apply(algebra.ge.ge.imply.ge.add), -Eq[-2].this.rhs, sets.el.given.et.split.interval.apply(Eq[-1])

    Eq << Eq[-4].this.lhs.apply(sets.is_nonpositive.imply.is_nonpositive_real, simplify=None)

    Eq << algebra.imply.gt.ceiling.apply(x)

    Eq << Eq[-3].this.lhs.apply(sets.el.imply.le.split.interval)

    Eq << Eq[-1].this.lhs.apply(algebra.is_nonpositive.imply.ceiling_is_nonpositive)

    Eq << algebra.imply.le.ceiling.apply(x)


if __name__ == '__main__':
    run()
