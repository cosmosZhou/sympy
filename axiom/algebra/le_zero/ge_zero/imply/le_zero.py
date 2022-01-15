from util import *


@apply
def apply(is_nonpositive, is_nonnegative_y):
    x = is_nonpositive.of(Expr <= 0)
    y = is_nonnegative_y.of(Expr >= 0)
    return LessEqual(x * y, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True)

    Eq << apply(x <= 0, y >= 0)

    Eq.is_zero = Infer(Equal(x, 0) & (y >= 0), x * y <= 0, plausible=True)

    Eq << Eq.is_zero.this.lhs.apply(algebra.et.imply.cond, index=0)

    Eq << Eq[-1].this.lhs * y

    Eq << algebra.infer.given.ou.apply(Eq[-1])

    Eq.is_negative = Infer((x < 0) & (y >= 0), x * y <= 0, plausible=True)

    Eq << Eq.is_negative.this.lhs.apply(algebra.lt_zero.ge_zero.imply.le_zero)

    Eq << algebra.infer.infer.imply.infer.ou.apply(Eq.is_zero, Eq.is_negative)

    Eq <<= Eq[0] & Eq[1]

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2018-02-10
