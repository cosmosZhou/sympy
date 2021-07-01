from util import *


@apply
def apply(given, upper=None):
    x, a = given.of(LessEqual)
    assert a <= upper

    return LessEqual(x, upper)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(domain=Interval(a, oo))

    Eq << apply(x <= a, b)

    Eq << LessEqual(a, b, plausible=True)

    Eq << algebra.le.le.imply.le.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
