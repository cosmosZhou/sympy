from util import *


@apply
def apply(given, lower=None, upper=None):
    assert given.is_GreaterEqual
    lhs, rhs = given.args
    if upper is not None:
        assert upper > lhs
        return Greater(upper, rhs)
        
    if lower is None:
        lower = rhs - 1

    assert rhs > lower
    return Greater(lhs, lower)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    Eq << apply(x >= y, y - 1)

    Eq << Greater(y, y - 1, plausible=True)

    Eq << algebra.ge.gt.imply.gt.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
