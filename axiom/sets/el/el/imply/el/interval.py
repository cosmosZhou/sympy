from util import *


@apply
def apply(contains1, contains2, w=None):
    x0, S = contains1.of(Element)
    x1, _S = contains2.of(Element)
    assert S == _S
    assert S.is_Interval

    assert w >= 0 and w <= 1
    return Element(x0 * w + x1 * (1 - w), S)


@prove
def prove(Eq):
    from axiom import algebra, sets

    a, b, x0, x1 = Symbol(real=True)
    domain = Interval(a, b, left_open=True)
    w = Symbol(domain=Interval(0, 1))
    Eq << apply(Element(x0, domain), Element(x1, domain), w)

    Eq << algebra.cond.given.et.suffice.split.apply(Eq[-1], cond=w > 0)

    Eq << (w <= 0).this.apply(algebra.le.imply.eq.squeeze.interval)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(algebra.et.given.et.subs.eq)

    Eq << algebra.suffice.given.et.suffice.apply(Eq[-1])

    Eq << algebra.cond.imply.suffice.apply(Eq[1], cond=w<=0)

    Eq << algebra.cond.given.et.suffice.split.apply(Eq[3], cond=w < 1)

    Eq.open_interval, Eq.ge = Eq[-2].this.apply(algebra.suffice.flatten), Eq[-1].this.apply(algebra.suffice.flatten)

    Eq << (w >= 1).this.apply(algebra.ge.imply.eq.squeeze.interval)

    Eq <<= Eq[-1] & Eq.ge

    Eq << Eq[-1].this.rhs.apply(algebra.et.given.et.subs.eq)

    Eq << algebra.suffice.given.et.suffice.apply(Eq[-1])

    Eq << algebra.cond.imply.suffice.apply(Eq[0], cond=w >= 1)

    Eq << Eq.open_interval.this.lhs.apply(sets.lt.gt.imply.el.interval, simplify=None)

    Eq << algebra.cond.imply.suffice.apply(Eq[0] & Eq[1], cond=Eq[-1].lhs)

    Eq << algebra.suffice.imply.suffice.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(sets.el.el.el.imply.el.interval.open)


if __name__ == '__main__':
    run()

