from util import *


@apply
def apply(le, ge, contains):
    _a, a = le.of(LessEqual)
    _b, b = ge.of(GreaterEqual)
    x, domain = contains.of(Element)
    a_, b_ = domain.of(Range)
    assert a == a_ and b == b_

    return Element(x, Range(_a, _b))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, a_quote, b_quote, x = Symbol(integer=True, given=True)
    Eq << apply(a_quote <= a, b_quote >= b, Element(x, Range(a, b)))

    Eq << sets.el_range.given.et.apply(Eq[-1])

    Eq << sets.el_range.imply.et.apply(Eq[2])

    Eq << algebra.ge.le.imply.ge.transit.apply(Eq[-2], Eq[0])
    Eq << algebra.lt.ge.imply.lt.transit.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2021-05-16
