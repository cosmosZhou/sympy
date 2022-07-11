from util import *


@apply
def apply(is_nonzero_x, is_nonzero_y):
    x = is_nonzero_x.of(Unequal[0])
    y = is_nonzero_y.of(Unequal[0])
    return Unequal(x * y, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(complex=True)
    Eq << apply(Unequal(x, 0), Unequal(y, 0))

    Eq << algebra.ne_zero.imply.gt_zero.abs.apply(Eq[0])

    Eq << algebra.ne_zero.imply.gt_zero.abs.apply(Eq[1])

    Eq << algebra.gt_zero.gt_zero.imply.gt_zero.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.abs)

    Eq << algebra.gt_zero.imply.ne_zero.apply(Eq[-1])

    Eq << algebra.abs_ne_zero.imply.ne_zero.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2018-03-19
# updated on 2022-04-03
