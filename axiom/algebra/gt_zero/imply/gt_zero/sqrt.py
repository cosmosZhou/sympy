from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)
    return Greater(sqrt(x), 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Greater(x, 0))

    Eq << algebra.gt_zero.imply.ge_zero.apply(Eq[0])

    Eq << algebra.ge_zero.imply.sqrt_ge_zero.apply(Eq[-1])

    Eq << algebra.gt_zero.imply.ne_zero.apply(Eq[0])

    Eq << algebra.ne_zero.imply.ne_zero.sqrt.apply(Eq[-1])
    Eq << algebra.ne_zero.ge_zero.imply.gt_zero.apply(Eq[-1], Eq[-3])


if __name__ == '__main__':
    run()
# created on 2018-07-17
