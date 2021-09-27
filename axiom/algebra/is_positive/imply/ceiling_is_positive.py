from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)

    return Greater(Ceiling(x), 0)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol(real=True, given=True)
    Eq << apply(x > 0)

    Eq << algebra.is_positive.imply.is_nonnegative.apply(Eq[0])

    Eq << algebra.is_nonnegative.imply.ceiling_is_nonnegative.apply(Eq[-1])

    Eq << ~Eq[1]

    Eq <<= Eq[-1] & Eq[-2]

    Eq << sets.ceiling_is_zero.imply.el.apply(Eq[-1])
    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()