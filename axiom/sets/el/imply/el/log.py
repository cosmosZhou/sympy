from util import *


@apply
def apply(given):
    e, interval = given.of(Element)
    assert interval.is_Interval
    left_open = interval.left_open
    right_open = interval.right_open

    start = interval.start
    if left_open:
        if start > 0:
            start = log(start)
        elif start == 0:
            start = -oo
        else:
            return
    else:
        assert start > 0
        start = log(start)

    stop = log(interval.stop)

    return Element(log(e), Interval(start, stop, left_open=left_open, right_open=right_open))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, b = Symbol(real=True)
    a = Symbol(real=True, positive=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << sets.el_interval.imply.et.apply(Eq[0])

    Eq << algebra.ge.imply.ge.log.apply(Eq[-2])

    Eq << algebra.ge.imply.gt_zero.apply(Eq[2])
    Eq << algebra.gt_zero.le.imply.le.log.apply(Eq[-1], Eq[3])

    Eq << sets.el_interval.given.et.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2021-03-05
