from util import *



@apply
def apply(given, t):
    assert given.is_Contains

    e, interval = given.args

    return Contains(e + t, interval + t)


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    t = Symbol.t(real=True)
    Eq << apply(Contains(x, Interval(a, b)), t)

    Eq << sets.contains.imply.et.split.interval.apply(Eq[0])

    Eq <<= Eq[-1] + t, Eq[-2] + t

    Eq << sets.le.ge.imply.contains.interval.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

