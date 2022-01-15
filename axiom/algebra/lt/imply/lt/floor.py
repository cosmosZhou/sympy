from util import *


@apply
def apply(given):
    x, y = given.of(Less)
    return Less(floor(x), y)


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True, given=True)

    Eq << apply(Less(x, y))

    Eq << algebra.imply.le.floor.apply(x)

    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()

# created on 2018-05-18
