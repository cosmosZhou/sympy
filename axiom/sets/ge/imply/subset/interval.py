from util import *


@apply
def apply(given):
    b, a = given.of(GreaterEqual)
    return Subset(Interval(b, a), Interval(a, b))


@prove
def prove(Eq):
    from axiom import sets

    x, y = Symbol(real=True, given=True)
    Eq << apply(x >= y)

    Eq << Eq[0].reversed
    Eq << sets.le.imply.subset.interval.apply(Eq[-1])


if __name__ == '__main__':
    run()
