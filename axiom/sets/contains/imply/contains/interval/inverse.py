from util import *


@apply
def apply(given):
    x, self = given.of(Contains)
    a, b = self.of(Interval)

    if a.is_positive:
        domain = Interval(1 / b, 1 / a, left_open=self.right_open, right_open=self.left_open)
    elif b.is_negative:
        domain = Interval(1 / a, 1 / b, left_open=self.right_open, right_open=self.left_open)

    return Contains(1 / x, domain)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol.x(real=True)
    a = Symbol.a(real=True, positive=True)
    b = Symbol.b(real=True)
    Eq << apply(Contains(x, Interval(a, b)))

    Eq << algebra.et.imply.conds.apply(sets.contains.imply.et.split.interval.apply(Eq[0]))

    Eq <<= algebra.ge.imply.le.inverse.apply(Eq[-1]), algebra.ge.imply.is_positive.apply(Eq[-1])

    Eq << algebra.is_positive.imply.is_positive.div.apply(Eq[-1])

    Eq <<= algebra.is_positive.le.imply.le.mul.apply(Eq[-1], Eq[2]), algebra.gt.le.imply.gt.transit.apply(Eq[-2], Eq[2])

    Eq << algebra.is_positive.imply.is_positive.div.apply(Eq[-1])

    Eq <<= algebra.is_positive.ge.imply.ge.mul.apply(Eq[-1], Eq[-3])
    Eq << sets.ge.le.imply.contains.interval.apply(Eq[-1], Eq[4])


if __name__ == '__main__':
    run()