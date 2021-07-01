from util import *


@apply
def apply(given):
    x = given.of(NotContains[Integers])

    return Equal(floor(-frac(x)), -1)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol.x(real=True)
    Eq << apply(NotContains(x, Integers))

    Eq << sets.notcontains.imply.contains.frac.apply(Eq[0])

    Eq << sets.contains.imply.contains.neg.apply(Eq[-1])

    Eq << sets.contains.imply.et.split.interval.apply(Eq[-1])

    Eq <<= algebra.lt.imply.lt.floor.apply(Eq[-1]), algebra.gt.imply.ge.floor.apply(Eq[-2])

    Eq << algebra.lt.imply.le.strengthen.apply(Eq[-2])

    Eq <<= Eq[-2] & Eq[-1]


if __name__ == '__main__':
    run()
