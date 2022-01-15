from util import *


@apply
def apply(given):
    x, y = given.of(LessEqual)
    return LessEqual(Floor(x), Floor(y))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x <= y)

    Eq << ~Eq[1]

    Eq << algebra.gt.imply.ge.strengthen.apply(Eq[-1])

    Eq << algebra.imply.le.floor.apply(x)

    Eq << algebra.ge.le.imply.ge.transit.apply(Eq[-2], Eq[-1])

    Eq << algebra.imply.lt.floor.apply(y)

    Eq << algebra.ge.lt.imply.gt.transit.apply(Eq[-2], Eq[-1])

    Eq <<= Eq[-1] & Eq[0]

    
    


if __name__ == '__main__':
    run()
# created on 2021-12-27

from . import integer
