from util import *


@apply
def apply(given):
    x = given.of(Ceiling < 0)
    return Less(x, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Less(Ceiling(x), 0))

    Eq << ~Eq[-1]

    Eq << algebra.ge_zero.imply.ceiling_ge_zero.apply(Eq[-1])


    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2019-03-11
