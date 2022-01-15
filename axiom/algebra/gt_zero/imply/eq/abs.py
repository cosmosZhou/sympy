from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)
    return Equal(abs(x), x)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True)

    Eq << apply(x > 0)

    Eq << algebra.gt.imply.ge.relax.apply(Eq[0])

    Eq << algebra.ge_zero.imply.eq.abs.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-06-28
