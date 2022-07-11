from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    a, b = domain.of(Interval)
    assert a + b == 0
    assert domain.left_open and domain.right_open

    return abs(x) < b


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, a = Symbol(real=True)
    Eq << apply(Element(x, Interval(-a, a, left_open=True, right_open=True)))

    Eq << algebra.lt_abs.given.et.apply(Eq[1])
    Eq << sets.el_interval.imply.et.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2021-03-12
