from util import *


@apply
def apply(le, ge, contains):
    _a, a = le.of(LessEqual)
    _b, b = ge.of(GreaterEqual)
    x, domain = contains.of(Element)
    a_, b_ = domain.of(Interval)
    assert a == a_ and b == b_

    return Element(x, Interval(_a, _b, left_open=domain.left_open, right_open=domain.right_open))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, a_quote, b_quote, x = Symbol(real=True, given=True)
    Eq << apply(a_quote <= a, b_quote >= b, Element(x, Interval(a, b, right_open=True)))

    Eq << sets.el_interval.given.et.apply(Eq[-1])

    Eq << sets.el_interval.imply.et.apply(Eq[2])

    Eq << algebra.ge.le.imply.ge.transit.apply(Eq[-2], Eq[0])
    Eq << algebra.lt.ge.imply.lt.transit.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2018-11-05
