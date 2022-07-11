from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    a, b = domain.of(Interval)
    assert a + b == 0
    assert domain.left_open and domain.right_open

    return x ** 2 < b ** 2


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, a = Symbol(real=True)
    Eq << apply(Element(x, Interval(-a, a, left_open=True, right_open=True)))

    Eq << sets.el_interval.imply.et.apply(Eq[0])

    Eq << algebra.gt.lt.imply.gt.transit.apply(Eq[-2], Eq[-1])

    Eq << algebra.gt.imply.gt_zero.apply(Eq[-1]) / 2

    Eq << algebra.gt_zero.imply.eq.abs.apply(Eq[-1])

    Eq << algebra.lt_square.given.et.lt.apply(Eq[1])

    Eq <<= Eq[-2].subs(Eq[-3]), Eq[-1].subs(Eq[-3])
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2020-11-26
