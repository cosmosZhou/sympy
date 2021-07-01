from util import *


@apply
def apply(given):
    a, b = given.of(LessEqual)
    return Subset(Interval(b, a), Interval(a, b))


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    Eq << apply(x <= y)

    Eq << sets.le.imply.eq.interval.apply(Eq[0])

    Eq << Eq[1].subs(Eq[-1])

    Eq << sets.imply.subset.intersection.apply(x, y)






if __name__ == '__main__':
    run()