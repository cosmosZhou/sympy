from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)
    return Element(sqrt(x), Reals)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol(real=True, given=True)
    Eq << apply(x > 0)

    Eq << algebra.gt_zero.imply.ge_zero.apply(Eq[0])

    Eq << sets.ge_zero.imply.sqrt_is_real.apply(Eq[-1], simplify=None)


if __name__ == '__main__':
    run()
# created on 2021-04-20
