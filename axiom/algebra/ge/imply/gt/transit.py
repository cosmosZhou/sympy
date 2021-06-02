from util import *


@apply
def apply(given, lower_bound=None):
    assert given.is_GreaterEqual
    lhs, rhs = given.args
    if lower_bound is None:
        lower_bound = rhs - 1

    assert rhs > lower_bound
    return Greater(lhs, lower_bound)


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
