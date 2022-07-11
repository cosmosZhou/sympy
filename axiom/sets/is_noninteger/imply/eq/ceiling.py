from util import *


@apply
def apply(given):
    x = given.of(NotElement[Integers])
    return Equal(ceiling(x), floor(x) + 1)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol(real=True)
    Eq << apply(NotElement(x, Integers))

    Eq << algebra.imply.ge.ceiling.apply(x)

    Eq << sets.notin.imply.gt_zero.frac.apply(Eq[0])

    Eq << Eq[-1].this.lhs.apply(algebra.frac.to.add)

    Eq << algebra.gt_zero.imply.gt.apply(Eq[-1])

    Eq.lt_floor = Eq[-1].reversed

    Eq << algebra.ge.gt.imply.gt.transit.apply(Eq[2], Eq[-1])

    Eq << algebra.gt.imply.ge.strengthen.apply(Eq[-1])

    Eq.gt_floor = algebra.imply.gt.floor.apply(x)

    Eq << Eq.gt_floor + 1

    Eq << algebra.ge.gt.imply.gt.transit.apply(Eq[-2], Eq[-1])

    Eq << algebra.imply.lt.ceiling.apply(x)

    Eq << sets.gt.lt.imply.el.interval.apply(Eq[-1], Eq[-2])

    Eq << sets.gt.lt.imply.el.interval.apply(Eq.gt_floor, Eq.lt_floor)

    Eq << sets.el.el.imply.el.sub.interval.apply(Eq[-2], Eq[-1])

    Eq << sets.el_interval.imply.et.apply(Eq[-1])

    Eq <<= algebra.gt.imply.ge.strengthen.apply(Eq[-2]), algebra.lt.imply.le.strengthen.apply(Eq[-1])

    Eq << algebra.ge.le.imply.eq.apply(Eq[-1], Eq[-2])
    Eq << Eq[-1].this.apply(algebra.eq.transport)


if __name__ == '__main__':
    run()
# created on 2018-05-17
