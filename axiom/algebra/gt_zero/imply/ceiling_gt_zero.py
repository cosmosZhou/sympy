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

    Eq << algebra.gt_zero.imply.ge_zero.apply(Eq[0])

    Eq << algebra.ge_zero.imply.ceiling_ge_zero.apply(Eq[-1])

    Eq << ~Eq[1]

    Eq <<= Eq[-1] & Eq[-2]

    Eq << sets.ceiling_is_zero.imply.el.apply(Eq[-1])
    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2019-08-12
