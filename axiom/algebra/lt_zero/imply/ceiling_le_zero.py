from util import *


@apply
def apply(given):
    x = given.of(Expr < 0)

    return LessEqual(Ceiling(x), 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    Eq << apply(x < 0)

    Eq << algebra.lt_zero.imply.le_zero.apply(Eq[0])

    Eq << algebra.le_zero.imply.ceiling_le_zero.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-01-18
