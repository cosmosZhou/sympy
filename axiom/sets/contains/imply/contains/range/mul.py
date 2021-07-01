from util import *


@apply
def apply(given, d):
    d = sympify(d)
    assert d.is_positive
    assert d.is_integer

    e, (a, b) = given.of(Contains[Range])

    e *= d

    return Contains(e, Range(a * d, (b - 1) * d + 1))


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol.x(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    d = Symbol.d(integer=True, positive=True)
    Eq << apply(Contains(x, Range(a, b)), d)

    Eq << sets.contains.imply.et.split.range.apply(Eq[0], right_open=False)

    Eq <<= Eq[-1] * d, Eq[-2] * d

    Eq << sets.ge.le.imply.contains.range.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()

