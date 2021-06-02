from util import *


@apply
def apply(given):
    x = given.of(NotContains[Integers])

    return Equal(ceiling(x), floor(x) + 1)


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(real=True)
    Eq << apply(NotContains(x, Integers))

    Eq << GreaterEqual(ceiling(x), x, plausible=True)

    Eq << sets.notcontains.imply.is_positive.frac.apply(Eq[0])

    Eq << Eq[-1].this.lhs.apply(algebra.frac.to.add)

    Eq << algebra.is_positive.imply.gt.apply(Eq[-1])

    Eq << algebra.ge.gt.imply.gt.transit.apply(Eq[2], Eq[-1])

    Eq << algebra.gt.imply.ge.strengthen.apply(Eq[-1])

    Eq << algebra.imply.le.ceiling.upper_bound.apply(x)

    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    run()
