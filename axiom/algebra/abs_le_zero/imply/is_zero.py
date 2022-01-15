from util import *


@apply
def apply(given):
    x = given.of(Abs <= 0)
    return Equal(x, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    Eq << apply(abs(x) <= 0)

    Eq << algebra.le_zero.imply.is_zero.apply(Eq[0])
    Eq << algebra.abs_is_zero.imply.is_zero.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-08-01
