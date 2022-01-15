from util import *


@apply
def apply(is_nonzero, is_nonpositive):
    x = is_nonzero.of(Unequal[0])
    is_nonpositive.of(x <= 0)
    return Less(x, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Unequal(x, 0), LessEqual(x, 0))

    Eq << ~Eq[-1]

    Eq << algebra.ge_zero.le_zero.imply.is_zero.apply(Eq[-1], Eq[1])

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2020-02-15
