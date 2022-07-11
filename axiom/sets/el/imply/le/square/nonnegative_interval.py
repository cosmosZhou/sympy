from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    m, M = interval.of(Interval)
    assert not interval.left_open
    assert not interval.right_open

    assert m.is_zero
    return LessEqual(x * x, M * M)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, M = Symbol(real=True)
    Eq << apply(Element(x, Interval(0, M)))

    Eq << sets.el_interval.imply.et.apply(Eq[0])



    Eq << algebra.ge_zero.le.imply.le.square.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-03-10
