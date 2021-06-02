from util import *


@apply
def apply(given):
    x, interval = given.of(Contains)
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
    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(Contains(x, Interval(a, b, right_open=True)))

    Eq << Eq[1].reversed

    Eq << Subset(Eq[0].rhs, Interval(a, oo, right_open=True), plausible=True)

    Eq << sets.contains.subset.imply.contains.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

