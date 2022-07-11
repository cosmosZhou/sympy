from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    a, b = interval.of(Interval)

    if interval.right_open:
        if interval.left_open:
            ...
        else:
            return LessEqual(a, x)
    else:
        return LessEqual(x, b)


@prove
def prove(Eq):
    from axiom import sets
    x, a, b = Symbol(real=True, given=True)
    Eq << apply(Element(x, Interval(a, b, right_open=True)))

    Eq << Eq[1].reversed

    Eq << Subset(Eq[0].rhs, Interval(a, oo, right_open=True), plausible=True)

    Eq << sets.el.subset.imply.el.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-04-04

from . import square
