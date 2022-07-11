from util import *


@apply
def apply(given):
    x, self = given.of(Element)
    a, b = self.of(Interval)

    if a.is_positive:
        domain = Interval(1 / b, 1 / a, left_open=self.right_open, right_open=self.left_open)
    elif b.is_negative:
        domain = Interval(1 / a, 1 / b, left_open=self.right_open, right_open=self.left_open)
    elif a == 0 and self.left_open:
        domain = Interval(1 / b, oo, left_open=self.right_open, right_open=self.left_open)
    elif b == 0 and self.right_open:
        domain = Interval(-oo, 1 / a, left_open=self.right_open, right_open=self.left_open)

    return Element(1 / x, domain)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, b = Symbol(real=True)
    a = Symbol(real=True, positive=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << sets.el_interval.imply.et.apply(Eq[0])

    Eq <<= algebra.ge.imply.le.inverse.apply(Eq[-2]), algebra.ge.imply.gt_zero.apply(Eq[-2])

    Eq << algebra.gt_zero.imply.gt_zero.div.apply(Eq[-1])

    Eq <<= algebra.gt_zero.le.imply.le.mul.apply(Eq[-1], Eq[3]), algebra.gt.le.imply.gt.transit.apply(Eq[-2], Eq[3])

    Eq << algebra.gt_zero.imply.gt_zero.div.apply(Eq[-1])

    Eq <<= algebra.gt_zero.ge.imply.ge.mul.apply(Eq[-1], Eq[-3])

    Eq << sets.ge.le.imply.el.interval.apply(Eq[-1], Eq[4])


if __name__ == '__main__':
    run()
# created on 2020-06-21
