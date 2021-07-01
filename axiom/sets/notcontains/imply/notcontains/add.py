from util import *


@apply
def apply(given, t):
    e, interval = given.of(NotContains)

    a, b = interval.args

    return NotContains(e + t, interval.copy(start=a + t, stop=b + t))


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    t = Symbol.t(real=True, given=True)

    Eq << apply(NotContains(x, Interval(a, b)), t)

    Eq << ~Eq[-1]

    Eq << sets.contains.imply.contains.sub.apply(Eq[-1], t)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

