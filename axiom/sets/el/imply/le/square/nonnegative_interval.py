from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    m, M = interval.of(Interval, None)
    assert not interval.left_open
    assert not interval.right_open

    assert m.is_zero
    return LessEqual(x * x, M * M)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, M = Symbol(real=True)
    Eq << apply(Element(x, Interval(0, M)))

    Eq << sets.el.imply.et.split.interval.apply(Eq[0])



    Eq << algebra.is_nonnegative.le.imply.le.square.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

