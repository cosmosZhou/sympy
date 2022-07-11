from util import *


@apply
def apply(given):
    abs_x, a = given.of(Less)
    x = abs_x.of(Abs)
    assert x.is_extended_real
    return Element(x, Interval(-a, a, left_open=True, right_open=True))


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, a = Symbol(real=True, given=True)
    Eq << apply(abs(x) < a)

    Eq << algebra.abs_lt.imply.et.apply(Eq[0])
    Eq << sets.el_interval.given.et.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2021-01-07
