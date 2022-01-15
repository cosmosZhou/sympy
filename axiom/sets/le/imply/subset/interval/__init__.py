from util import *


@apply
def apply(given):
    a, b = given.of(LessEqual)
    return Subset(Interval(b, a), Interval(a, b))


@prove
def prove(Eq):
    from axiom import sets

    x, y = Symbol(real=True, given=True)
    Eq << apply(x <= y)

    Eq << sets.le.imply.eq.interval.apply(Eq[0])

    Eq << Eq[1].subs(Eq[-1])

    Eq << sets.imply.subset.intersect.apply(x, y)


if __name__ == '__main__':
    run()
from . import negativeInfinity
from . import infinity
from . import upper
from . import lower
# created on 2020-06-03
