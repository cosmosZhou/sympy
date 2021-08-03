from util import *



@apply
def apply(given, d):
    e, interval = given.of(NotContains)
    d = sympify(d)
    assert d.is_positive

    a, b = interval.of(Interval)

    e *= d

    return NotContains(e, interval.copy(start=a * d, stop=b * d))


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)

    d = Symbol.d(real=True, positive=True, given=True)

    Eq << apply(NotContains(x, Interval(a, b, right_open=True)), d)

    Eq << ~Eq[-1]

    Eq << sets.contains.imply.contains.div.interval.apply(Eq[-1], d)

    Eq <<= Eq[-1] & Eq[0]

if __name__ == '__main__':
    run()

