from util import *


@apply
def apply(ou):
    x, y = ou.of(Unequal[0] | Unequal[0])
    return Greater(x ** 2 + y ** 2, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(Unequal(x, 0) | Unequal(y, 0))

    Eq << Equal(x ** 2 + y ** 2, 0).this.apply(algebra.poly_is_zero.imply.et.is_zero)

    Eq.is_nonzero = algebra.cond.cond.imply.cond.subs.apply(Eq[0], Eq[-1], invert=True)

    Eq <<= algebra.imply.ge_zero.square.apply(x), algebra.imply.ge_zero.square.apply(y)

    Eq << Eq[-1] + Eq[-2]
    Eq << algebra.ne_zero.ge_zero.imply.gt_zero.apply(Eq.is_nonzero, Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-07-15
