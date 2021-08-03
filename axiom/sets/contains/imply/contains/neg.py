from util import *


@apply
def apply(given):
    e, interval = given.of(Contains)

    return Contains(-e, -interval)


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(Contains(x, Interval(a, b)))

    Eq << sets.contains.imply.et.split.interval.apply(Eq[0])

    Eq <<= Eq[-1].reversed, Eq[-2].reversed

    Eq << sets.contains.given.et.split.interval.apply(Eq[1])


if __name__ == '__main__':
    run()

