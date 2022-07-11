from util import *


@apply
def apply(given):
    abs_x, a = given.of(Less)
    x = abs_x.of(Abs)
    assert x.is_extended_real
    return Element(x, Interval(-a, a, left_open=True, right_open=True))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(abs(x) < a)

    Eq << sets.el_interval.imply.et.apply(Eq[1])
    Eq << algebra.lt.gt.imply.lt.abs.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2020-04-24
