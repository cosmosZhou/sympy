from util import *


@apply
def apply(given):
    x = given.of(NotElement[Integers])

    return Greater(frac(x), 0)


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol(real=True, given=True)
    Eq << apply(NotElement(x, Integers))

    Eq << sets.notin.imply.is_nonzero.frac.apply(Eq[0])

    Eq << Element(frac(x), Interval(0, 1, right_open=True), plausible=True)

    Eq << sets.ne.el.imply.el.apply(Eq[-2], Eq[-1])

    Eq << sets.el.imply.et.split.interval.apply(Eq[-1])

if __name__ == '__main__':
    run()
