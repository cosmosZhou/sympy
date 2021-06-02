from util import *


@apply
def apply(given):
    x = given.of(NotContains[Integers])

    return Contains(frac(x), Interval(0, 1, left_open=True, right_open=True))


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(real=True)
    Eq << apply(NotContains(x, Integers))

    Eq << sets.notcontains.imply.ne_0.frac.apply(Eq[0])

    Eq << Contains(frac(x), Interval(0, 1, right_open=True), plausible=True)

    Eq << sets.ne.contains.imply.contains.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
