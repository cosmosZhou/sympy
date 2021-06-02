from util import *


@apply
def apply(given, d):
    d = sympify(d)
    assert d.is_positive
    assert d.is_integer

    e, (a, b) = given.of(Contains[Range])
    e /= d
    # assert e.is_integer

    b -= 1

    return Contains(e, Range(start=ceiling(a / d), stop=b // d + 1))


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)

    d = Symbol.d(integer=True, positive=True)

    Eq << apply(Contains(d * x, Range(a, b + 1)), d)

    Eq << sets.contains.imply.et.split.range.apply(Eq[0])

    Eq << algebra.et.imply.conds.apply(Eq[-1])

    Eq << algebra.lt.imply.le.strengthen.apply(Eq[-2])

    Eq <<= Eq[-2] / d, Eq[-1] / d

    Eq <<= algebra.ge.imply.ge.ceiling.apply(Eq[-2]), algebra.le.imply.le.floor.apply(Eq[-1])

    Eq << sets.ge.le.imply.contains.range.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

