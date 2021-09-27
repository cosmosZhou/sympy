from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    a, b = domain.of(Interval)
    b = Max(abs(a), abs(b))
    return Element(sqrt(b ** 2 - x ** 2), Interval(0, b))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, x = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << sets.el.given.et.split.interval.apply(Eq[1])

    Eq << sets.el.imply.le.max.apply(Eq[0])

    Eq << algebra.le.imply.le.square.apply(Eq[-1]).reversed

    Eq << algebra.ge.imply.is_nonnegative.apply(Eq[-1])

    Eq << algebra.is_nonnegative.imply.sqrt_is_nonnegative.apply(Eq[-1])

    Eq << LessEqual(-x ** 2, 0, plausible=True)

    Eq << algebra.le.imply.le.add.apply(Eq[-1], Max(abs(a), abs(b)) ** 2)

    Eq << algebra.is_nonnegative.le.imply.le.sqrt.apply(Eq[-3], Eq[-1])


if __name__ == '__main__':
    run()