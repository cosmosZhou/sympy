from util import *


@apply
def apply(given):
    e, interval = given.of(Element)

    return Element(-e, -interval)


@prove
def prove(Eq):
    from axiom import sets

    x, a, b = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << sets.el.imply.et.split.interval.apply(Eq[0])

    Eq <<= Eq[-1].reversed, Eq[-2].reversed

    Eq << sets.el.given.et.split.interval.apply(Eq[1])


if __name__ == '__main__':
    run()

