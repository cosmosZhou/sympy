from util import *


@apply
def apply(given):
    x, y = given.of(Greater)
    assert y.is_integer
    return GreaterEqual(floor(x), y)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True, given=True)
    y = Symbol(integer=True, given=True)
    Eq << apply(x > y)

    Eq << algebra.imply.gt.floor.apply(x)

    Eq << Eq[0] - 1

    Eq << algebra.gt.gt.imply.gt.transit.apply(Eq[-1], Eq[-2])

    Eq << algebra.gt.imply.ge.strengthen.apply(Eq[-1])


if __name__ == '__main__':
    run()

