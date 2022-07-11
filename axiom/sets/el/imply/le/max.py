from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    a, b = domain.of(Interval)
    b = Max(abs(a), abs(b))
    return abs(x) <= b


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, x = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << sets.el_interval.imply.et.apply(Eq[0])

    Eq << algebra.le_abs.given.et.apply(Eq[1])

    Eq << algebra.imply.le.abs.apply(b)

    Eq << LessEqual(abs(b), Max(abs(a), abs(b)), plausible=True)

    Eq << algebra.le.le.imply.le.transit.apply(Eq[-2], Eq[-1])

    Eq << algebra.le.le.imply.le.transit.apply(Eq[3], Eq[-1])

    Eq << algebra.imply.ge.abs.apply(a)

    Eq << GreaterEqual(-abs(a), -Max(abs(a), abs(b)), plausible=True)

    Eq << algebra.ge.ge.imply.ge.transit.apply(Eq[-2], Eq[-1])
    Eq << algebra.ge.ge.imply.ge.transit.apply(Eq[2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-06-30
