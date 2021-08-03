from util import *


@apply
def apply(given, d):

    d = sympify(d)
    assert d.is_positive
    assert d.is_integer

    e, interval = given.of(NotContains)

    a, b = interval.of(Range)
    e /= d

    assert e.is_integer
    b -= 1

    return NotContains(e, Range(start=ceiling(a / d), stop=b // d + 1))


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(integer=True, given=True)
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)

    d = Symbol.d(integer=True, positive=True, given=True)

    Eq << apply(NotContains(d * x, Range(a, b + 1)), d)

    Eq << ~Eq[-1]

    Eq.contains = sets.contains.imply.contains.mul.range.apply(Eq[-1], d)

    Eq << algebra.imply.le.floor.apply(b, d)

    Eq << algebra.imply.ge.ceiling.apply(a, d)

    Eq << sets.le.ge.imply.subset.range.apply(Eq[-2], Eq[-1])

    Eq << sets.contains.subset.imply.contains.apply(Eq.contains, Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

