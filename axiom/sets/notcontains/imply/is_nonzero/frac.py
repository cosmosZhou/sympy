from util import *


@apply
def apply(given):
    x = given.of(NotContains[Integers])

    return Unequal(frac(x), 0)


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol.x(real=True, given=True)
    Eq << apply(NotContains(x, Integers))

    Eq << ~Eq[1]

    Eq << sets.is_zero.imply.contains.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
