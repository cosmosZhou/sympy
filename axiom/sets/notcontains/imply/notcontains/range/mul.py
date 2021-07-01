from util import *


@apply
def apply(given, d):
    e, interval = given.of(NotContains)
    d = sympify(d)
    assert d.is_positive

    a, b = interval.of(Range)

    e *= d

    return NotContains(e, interval.copy(start=a * d, stop=(b - 1) * d + 1))


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(integer=True, given=True)
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)

    d = Symbol.d(integer=True, positive=True, given=True)

    Eq << apply(NotContains(x, Range(a, b)), d)

    Eq << ~Eq[-1]

    Eq << sets.contains.imply.contains.range.div.apply(Eq[-1], d)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

