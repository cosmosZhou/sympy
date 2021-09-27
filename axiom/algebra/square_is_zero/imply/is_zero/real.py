from util import *


@apply
def apply(given):
    x = given.of(Equal[Expr ** 2, 0])
    assert x.is_extended_real
    return Equal(x, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Equal(x ** 2, 0))

    Eq << algebra.eq.imply.eq.pow.apply(Eq[0], exp=S.One / 2)

    Eq << algebra.abs_is_zero.imply.is_zero.real.apply(Eq[-1])


if __name__ == '__main__':
    run()
