from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    m, M = interval.of(Interval)
    assert interval.left_open
    assert interval.right_open

    return Less(x * x, Max(m * m, M * M))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, m, M = Symbol(real=True)
    Eq << apply(Element(x, Interval(m, M, left_open=True, right_open=True)))

    Eq << sets.el_interval.imply.et.apply(Eq[0])

    Eq << algebra.lt.gt.imply.lt.square.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2019-08-31
