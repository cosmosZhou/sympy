from util import *


@apply
def apply(given):
    n, b = given.of(Less)
    assert n.is_finite
    return Element(n, Interval(-oo, oo))


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(complex=True, given=True)
    b = Symbol(real=True, given=True)
    Eq << apply(x < b)

    Eq << sets.lt.imply.el.interval.apply(Eq[0])

    Eq << sets.el.imply.el.relax.apply(Eq[-1], Interval(-oo, oo), simplify=None)


if __name__ == '__main__':
    run()
# created on 2020-04-12
