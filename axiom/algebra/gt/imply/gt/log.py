from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Greater)
    assert rhs > 0

    return Greater(log(lhs), log(rhs))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, given=True)
    y = Symbol(positive=True, given=True)
    Eq << apply(Greater(x, y))

    Eq << GreaterEqual(y, 0, plausible=True)

    Eq << algebra.gt.ge.imply.gt.transit.apply(Eq[0], Eq[-1])

    Eq << algebra.gt.imply.ne.apply(Eq[-1])

    Eq <<= ~Eq[1] & Eq[-1]

    Eq << algebra.et.imply.et.apply(Eq[-1])

    Eq << algebra.le.imply.le.exp.apply(Eq[-1])

    Eq << ~Eq[-1]
    


if __name__ == '__main__':
    run()
# created on 2022-03-31
# updated on 2022-04-01
