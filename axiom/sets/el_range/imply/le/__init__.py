from util import *


@apply
def apply(given):
    x, (a, b) = given.of(Element[Range])

    return LessEqual(a, x)


@prove
def prove(Eq):
    from axiom import sets
    x, a, b = Symbol(integer=True, given=True)
    Eq << apply(Element(x, Range(a, b)))

    Eq << Eq[1].reversed

    Eq << Subset(Eq[0].rhs, Range(a, oo), plausible=True)

    Eq << sets.el.subset.imply.el.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-02-16
from . import stop
