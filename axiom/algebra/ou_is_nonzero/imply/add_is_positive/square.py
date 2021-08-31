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

    Eq << Equal(x ** 2 + y ** 2, 0).this.apply(algebra.add_is_zero.imply.et.is_zero)

    Eq.is_nonzero = algebra.cond.cond.imply.cond.subs.apply(Eq[0], Eq[-1], invert=True)

    Eq <<= algebra.imply.is_nonnegative.square.apply(x), algebra.imply.is_nonnegative.square.apply(y)

    Eq << Eq[-1] + Eq[-2]
    Eq << algebra.is_nonzero.is_nonnegative.imply.is_positive.apply(Eq.is_nonzero, Eq[-1])


if __name__ == '__main__':
    run()