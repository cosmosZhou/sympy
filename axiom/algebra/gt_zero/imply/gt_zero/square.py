from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)

    return Greater(x * x, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    Eq << apply(x > 0)
    Eq << algebra.gt_zero.gt_zero.imply.gt_zero.apply(Eq[0], Eq[0])


if __name__ == '__main__':
    run()
# created on 2018-06-05
