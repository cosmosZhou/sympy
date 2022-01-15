from util import *


@apply
def apply(is_nonzero, is_nonpositive):
    x = is_nonzero.of(Unequal[0])
    is_nonpositive.of(x >= 0)
    return Greater(x, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Unequal(x, 0), GreaterEqual(x, 0))

    Eq << ~Eq[-1]

    Eq << algebra.le_zero.ge_zero.imply.is_zero.apply(Eq[-1], Eq[1])

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2018-07-15
