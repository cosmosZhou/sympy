from util import *


@apply
def apply(given):
    x = given.of(Expr < 0)

    return Less(Floor(x), 0)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol(real=True, given=True)
    Eq << apply(x < 0)

    Eq << algebra.is_negative.imply.is_nonpositive.apply(Eq[0])

    Eq << algebra.is_nonpositive.imply.floor_is_nonpositive.apply(Eq[-1])

    Eq << ~Eq[1]

    Eq <<= Eq[-1] & Eq[-2]

    Eq << sets.floor_is_zero.imply.el.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()