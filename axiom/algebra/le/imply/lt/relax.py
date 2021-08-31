from util import *


@apply
def apply(given, upper=None, lower=None):
    x, a = given.of(LessEqual)
    if upper is not None:
        assert a < upper
        return Less(x, upper)
    if lower is not None:
        assert lower < x
        return Less(lower, a)


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(real=True)
    b = Symbol(domain=Interval(a, oo, left_open=True))
    Eq << apply(x <= a, b)

    Eq << Less(a, b, plausible=True)

    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
