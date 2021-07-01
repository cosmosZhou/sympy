from util import *


@apply
def apply(given):
    e, interval = given.of(NotContains)

    return NotContains(-e, -interval)


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(NotContains(x, Interval(a, b)))

    Eq << ~Eq[-1]

    Eq << sets.contains.imply.contains.neg.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

