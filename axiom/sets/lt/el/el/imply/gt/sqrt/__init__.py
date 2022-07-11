from util import *


@apply
def apply(lt, contains, contains_y):
    x, domain_x = contains.of(Element)
    y, domain_y = contains_y.of(Element)
    assert domain_x in Interval(-1, 1)
    assert domain_y in Interval(-1, 1, right_open=True)
    S[x], S[y] = lt.of(Less)
    return y * sqrt(1 - x ** 2) > x * sqrt(1 - y ** 2)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, y = Symbol(real=True)
    Eq << apply(x < y, Element(x, Interval(-1, 1)), Element(y, Interval(-1, 1, right_open=True)))

    Eq << sets.lt.el.imply.lt.transit.apply(Eq[0], Eq[2])

    Eq.x_contains = sets.lt.el.imply.el.intersect.apply(Eq[-1], Eq[1])

    Eq << sets.gt.el.imply.gt.transit.apply(Eq[0].reversed, Eq[1])

    Eq.y_contains = sets.gt.el.imply.el.intersect.apply(Eq[-1], Eq[2])

    Eq << algebra.cond.given.et.infer.split.apply(Eq[3], cond=Equal(x, -1))

    Eq << algebra.infer.given.infer.subs.apply(Eq[-2])

    Eq << algebra.infer.given.cond.apply(Eq[-1])

    Eq << -sets.el.imply.lt.square.apply(Eq.y_contains) + 1

    Eq << algebra.gt_zero.imply.gt_zero.sqrt.apply(Eq[-1])

    Eq << algebra.cond.imply.infer.apply(Eq.x_contains, cond=Eq[-4].lhs)

    Eq << algebra.infer.imply.infer.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(sets.ne.el.imply.el)

    Eq << algebra.cond.infer.imply.infer.et.rhs.apply(Eq.y_contains & Eq[0], Eq[-1])
    Eq << Eq[-1].this.rhs.apply(sets.lt.el.el.imply.gt.sqrt.open)


if __name__ == '__main__':
    run()
from . import open
# created on 2020-11-29
