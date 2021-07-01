from util import *


@apply
def apply(given):
    x, (a, b) = given.of(Contains[Range])

    return LessEqual(x, b - 1)


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(real=True, given=True)
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    Eq << apply(Contains(x, Range(a, b)))

    Eq << Subset(Eq[0].rhs, Interval(-oo, b - 1), plausible=True)

    Eq << sets.contains.subset.imply.contains.apply(Eq[0], Eq[-1])

#     Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

