from util import *


@apply
def apply(is_nonzero_x, is_nonzero_y):
    x = is_nonzero_x.of(Unequal[0])
    y = is_nonzero_y.of(Unequal[0])
    return Unequal(x * y, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(complex=True)
    y = Symbol.y(complex=True)
    Eq << apply(Unequal(x, 0), Unequal(y, 0))

    Eq << algebra.is_nonzero.imply.abs_is_positive.apply(Eq[0])

    Eq << algebra.is_nonzero.imply.abs_is_positive.apply(Eq[1])

    Eq << algebra.is_positive.is_positive.imply.is_positive.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.abs)

    Eq << algebra.is_positive.imply.is_nonzero.apply(Eq[-1])

    Eq << algebra.is_nonzero.imply.is_nonzero.strip.abs.apply(Eq[-1])


if __name__ == '__main__':
    run()
