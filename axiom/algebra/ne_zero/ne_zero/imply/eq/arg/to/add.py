from util import *


@apply
def apply(is_nonzero_x, is_nonzero_y):
    x = is_nonzero_x.of(Unequal[0])
    y = is_nonzero_y.of(Unequal[0])
    s = Arg(x) + Arg(y)
    return Equal(Arg(x * y), s - Ceiling(s / (2 * S.Pi) - S.One / 2) * 2 * S.Pi)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(complex=True, given=True)
    Eq << apply(Unequal(x, 0), Unequal(y, 0))

    Eq << algebra.ne_zero.imply.gt_zero.abs.apply(Eq[0])

    Eq << algebra.ne_zero.imply.gt_zero.abs.apply(Eq[1])

    Eq.abs_is_positive = Eq[-1] * Eq[-2]

    Eq <<= algebra.expr.to.mul.expi.apply(x), algebra.expr.to.mul.expi.apply(y)

    Eq << Eq[-1] * Eq[-2]

    Eq << algebra.eq.imply.eq.arg.apply(Eq[-1])

    Eq << algebra.gt_zero.imply.eq.arg.apply(Eq.abs_is_positive, Mul(*Eq[-1].rhs.arg.args[2:]))

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.arg.apply(algebra.mul.to.exp)

    Eq << Eq[-1].this.rhs.apply(algebra.arg_expi.to.add.ceiling)


if __name__ == '__main__':
    run()
# created on 2018-10-25
