from util import *


@apply
def apply(given, d):
    d = sympify(d)
    assert d.is_positive

    e, interval = given.of(Contains)

    a, b = interval.of(Interval)

    return Contains(e / d, interval.copy(start=a / d, stop=b / d))


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
#     t = Symbol.t(real=True)
    d = 2
    Eq << apply(Contains(x, Interval(a, b)), d)

    Eq << algebra.et.imply.conds.apply(sets.contains.imply.et.split.interval.apply(Eq[0]))

    Eq <<= Eq[-2] / d, Eq[-1] / d

    Eq << sets.contains.given.et.split.interval.apply(Eq[1])

    Eq << algebra.et.given.conds.apply(Eq[-1])


if __name__ == '__main__':
    run()

