from util import *


@apply
def apply(given):
    x = given.of(Unequal[0])
    return Greater(abs(x), 0)


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol(complex=True)
    Eq << apply(Unequal(a, 0))

    Eq << algebra.ne_zero.imply.ne_zero.abs.apply(Eq[0])

    Eq << algebra.ne_zero.imply.gt_zero.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-03-18
