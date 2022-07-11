from util import *


@apply
def apply(lt, contains_y):
    y, _b = lt.of(Less)
    _y, domain = contains_y.of(Element)
    assert y == _y
    a, b = domain.of(Interval)
    b = Min(b, _b)
    return Element(y, Interval(a, b, left_open=domain.left_open, right_open=True))


@prove
def prove(Eq):
    from axiom import sets

    a, b, x, y = Symbol(real=True)
    Eq << apply(x < b, Element(x, Interval(a, b)))

    Eq << sets.el_interval.given.et.apply(Eq[2])

    Eq << sets.el_interval.imply.et.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2018-06-22
