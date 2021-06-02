from util import *


@apply
def apply(given):
    assert given.is_Contains
    x, interval = given.args
    a, b = interval.of(Range)

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
    x = Symbol.x(integer=True, given=True)
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    Eq << apply(Contains(x, Range(a, b)))

    Eq << Subset(Eq[0].rhs, Range(a, oo), plausible=True)

    Eq << sets.contains.subset.imply.contains.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

