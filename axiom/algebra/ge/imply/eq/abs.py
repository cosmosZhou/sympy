from util import *


@apply
def apply(given):
    x, y = given.of(GreaterEqual)
    return Equal(abs(x - y), x - y)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(x >= y)

    Eq << algebra.ge.imply.ge_zero.apply(Eq[0])
    Eq << algebra.ge_zero.imply.eq.abs.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-05-25
