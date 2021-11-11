from util import *


@apply
def apply(given):
    x = given.of(Equal[Expr ** 2, 0])
    return Equal(x, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(complex=True, given=True)
    Eq << apply(Equal(x ** 2, 0))

    Eq << Eq[0].this.lhs.base.apply(algebra.expr.to.mul.expi)

    Eq << algebra.mul_is_zero.imply.ou.is_zero.apply(Eq[-1])

    Eq << algebra.square_is_zero.imply.is_zero.real.apply(Eq[-1])
    Eq << algebra.abs_is_zero.imply.is_zero.apply(Eq[-1])


if __name__ == '__main__':
    run()

from . import real
# created on 2018-11-11
# updated on 2018-11-11
