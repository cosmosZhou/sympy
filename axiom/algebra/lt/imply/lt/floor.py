from util import *


@apply
def apply(given):
    x, y = given.of(Less)
    return Less(floor(x), y)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)

    Eq << apply(Less(x, y))

    Eq << algebra.imply.le.floor.apply(x)

    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()

