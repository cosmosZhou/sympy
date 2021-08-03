from util import *


@apply
def apply(given):
    x = given.of(Ceiling < 0)
    return Less(x, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True, given=True)
    Eq << apply(Less(Ceiling(x), 0))

    Eq << ~Eq[-1]

    Eq << algebra.is_nonnegative.imply.ceiling_is_nonnegative.apply(Eq[-1])
    

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()