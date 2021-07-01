from util import *


@apply
def apply(given, d):
    d = sympify(d)
    assert d.is_positive

    e, interval = given.of(Contains)

    a, b = interval.of(Interval)

    e *= d

    return Contains(e, interval.copy(start=a * d, stop=b * d))


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    d = Symbol.d(real=True, positive=True)
    Eq << apply(Contains(x, Interval(a, b, right_open=True)), d)

    Eq << sets.contains.imply.et.split.interval.apply(Eq[0])

    Eq <<= Eq[-2] * d, Eq[-1] * d

    Eq << sets.ge.lt.imply.contains.interval.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

