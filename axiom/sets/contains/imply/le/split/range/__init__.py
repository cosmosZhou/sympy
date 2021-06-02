from util import *


@apply
def apply(given):
    x, (a, b) = given.of(Contains[Range])

    return LessEqual(a, x)


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(integer=True, given=True)
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    Eq << apply(Contains(x, Range(a, b)))

    Eq << Eq[1].reversed

    Eq << Subset(Eq[0].rhs, Range(a, oo), plausible=True)

    Eq << sets.contains.subset.imply.contains.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

from . import stop
