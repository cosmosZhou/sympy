from util import *


@apply
def apply(le, contains_y):
    if le.is_Element:
        le, contains_y = contains_y, le
    y, a = le.of(LessEqual)
    _y, domain = contains_y.of(Element)
    assert y == _y
    b, c = domain.of(Interval)
    a = Min(c, a)
    return Element(y, Interval(b, a, left_open=domain.left_open, right_open=domain.right_open))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, c, x, y = Symbol(real=True)
    Eq << apply(x <= a, Element(x, Interval(b, c)))

    Eq << sets.el_interval.given.et.apply(Eq[2])

    Eq << sets.el_interval.imply.et.apply(Eq[1])

    Eq << algebra.le.le.imply.le.min.rhs.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2020-11-27
