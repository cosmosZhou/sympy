from util import *


@apply
def apply(given, upper=None):
    x, a = given.of(LessEqual)
    assert a < upper

    return Less(x, upper)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(domain=Interval(a, oo, left_open=True))

    Eq << apply(x <= a, b)

    Eq << Less(a, b, plausible=True)

    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
