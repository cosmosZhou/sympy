from util import *


@apply
def apply(given):
    x, interval = given.of(Contains)
    a, b = interval.of(Interval)

    if interval.left_open:
        if interval.right_open:
            ...
        else:
            return GreaterEqual(b, x)
    else:
        return GreaterEqual(x, a)


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(Contains(x, Interval(a, b, right_open=True)))

    Eq << Subset(Eq[0].rhs, Interval(a, oo, right_open=True), plausible=True)

    Eq << sets.contains.subset.imply.contains.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

