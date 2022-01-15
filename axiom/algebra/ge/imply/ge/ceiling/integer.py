from util import *


@apply
def apply(given):
    x, y = given.of(GreaterEqual)
    assert x.is_integer
    assert y.is_real

    return GreaterEqual(x, ceiling(y))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(integer=True, given=True)
    y = Symbol(real=True, given=True)

    Eq << apply(x >= y)

    Eq << ~Eq[1]

    Eq << algebra.lt.imply.le.strengthen.apply(Eq[-1])

    Eq << algebra.ge.le.imply.le.transit.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].reversed - (y - 1)

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.frac)


if __name__ == '__main__':
    run()

# created on 2018-05-22
