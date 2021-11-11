from util import *


@apply
def apply(given, lower=None, upper=None, plus=False):
    lhs, rhs = given.of(GreaterEqual)
    if upper is not None:
        assert upper > lhs
        lhs = upper
    elif lower is not None:
        assert rhs > lower
        rhs = lower
    elif plus:
        lhs += 1
    else:
        rhs -= 1


    return Greater(lhs, rhs)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x >= y, y - 1)

    Eq << Greater(y, y - 1, plausible=True)

    Eq << algebra.ge.gt.imply.gt.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-05-29
# updated on 2018-05-29
