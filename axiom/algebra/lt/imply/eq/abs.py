from util import *


@apply
def apply(given):
    x, y = given.of(Less)
    return Equal(abs(x - y), -x + y)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(x < y)

    Eq << algebra.lt.imply.is_negative.apply(Eq[0])

    Eq << algebra.is_negative.imply.eq.abs.apply(Eq[-1])


if __name__ == '__main__':
    run()