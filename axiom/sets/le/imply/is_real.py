from util import *


@apply
def apply(given):
    n, b = given.of(LessEqual)

    return Contains(n, Interval(-oo, oo))


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(complex=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(x <= b)
    
    Eq << sets.le.imply.contains.interval.apply(Eq[0])
    Eq << sets.contains.imply.contains.relaxed.apply(Eq[-1], Interval(-oo, oo))


if __name__ == '__main__':
    run()