from util import *


@apply
def apply(given):
    x = given.of(NotContains[Integers])

    return Greater(frac(x), 0)


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(real=True, given=True)
    Eq << apply(NotContains(x, Integers))

    Eq << sets.notcontains.imply.ne_0.frac.apply(Eq[0])

    Eq << Contains(frac(x), Interval(0, 1, right_open=True), plausible=True)

    Eq << sets.ne.contains.imply.contains.apply(Eq[-2], Eq[-1])

    Eq << sets.contains.imply.et.split.interval.apply(Eq[-1])

if __name__ == '__main__':
    run()
