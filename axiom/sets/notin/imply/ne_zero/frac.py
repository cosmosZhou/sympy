from util import *


@apply
def apply(given):
    x = given.of(NotElement[Integers])

    return Unequal(frac(x), 0)


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(real=True, given=True)
    Eq << apply(NotElement(x, Integers))

    Eq << ~Eq[1]

    Eq << sets.frac_is_zero.imply.el.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2018-05-10
