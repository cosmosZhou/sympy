from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    m, M = interval.of(Interval)
    assert not interval.left_open
    assert not interval.right_open
    assert M.is_zero
    return LessEqual(x * x, m * m)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, m = Symbol(real=True)
    Eq << apply(Element(x, Interval(m, 0)))

    Eq << sets.el_interval.imply.et.apply(Eq[0])

    Eq << algebra.le_zero.ge.imply.le.square.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()

# created on 2021-03-11
