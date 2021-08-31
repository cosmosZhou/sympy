from util import *


@apply
def apply(given):
    n, b = given.of(GreaterEqual)

    return Element(n, Interval(-oo, oo))


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol(complex=True, given=True)
    b = Symbol(real=True, given=True)
    Eq << apply(x >= b)

    Eq << sets.ge.imply.el.interval.apply(Eq[0])
    Eq << sets.el.imply.el.relax.apply(Eq[-1], Interval(-oo, oo))


if __name__ == '__main__':
    run()
