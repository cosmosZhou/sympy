from util import *


@apply
def apply(gt, contains_y):
    y, _a = gt.of(Greater)
    _y, domain = contains_y.of(Element)
    assert y == _y
    a, b = domain.of(Interval)
    a = Max(a, _a)
    return Element(y, Interval(a, b, left_open=True, right_open=domain.right_open))


@prove
def prove(Eq):
    from axiom import sets

    a, b, x, y = Symbol(real=True)
    Eq << apply(x > a, Element(x, Interval(a, b)))

    Eq << sets.el_interval.given.et.apply(Eq[2])

    Eq << sets.el_interval.imply.et.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2018-06-21
