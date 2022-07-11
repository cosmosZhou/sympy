from util import *


@apply
def apply(gt_zero, x=None):
    b, (a, c) = gt_zero.of(Expr ** 2 - 4 * Expr * Expr > 0)
    assert x.is_real
    assert a.is_real and b.is_real and c.is_real
    return Any[x](a * x ** 2 + b * x + c > 0)


@prove
def prove(Eq):
    from axiom import algebra

    a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(b ** 2 - 4 * a * c > 0, x=x)

    Eq << algebra.cond.given.et.infer.split.apply(Eq[1], cond=Unequal(a, 0))

    Eq << algebra.infer.given.infer.subs.apply(Eq[-1])

    Eq << algebra.cond.imply.infer.apply(Eq[0], cond=Equal(a, 0))

    Eq << algebra.infer.imply.infer.subs.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.gt_zero.imply.ne_zero)

    Eq << Eq[-1].this.rhs.apply(algebra.ne_zero.imply.ne_zero.sqrt)

    Eq << Eq[-1].this.rhs.apply(algebra.abs_ne_zero.imply.ne_zero)

    Eq << Eq[-1].this.rhs.apply(algebra.ne_zero.imply.any.gt_zero, x=x, b=c)

    Eq << algebra.cond.imply.infer.et.apply(Eq[0], cond=Eq[2].lhs)

    Eq << Eq[-1].this.rhs.apply(algebra.ne_zero.add_gt_zero.imply.any.gt_zero, x=x)

    


if __name__ == '__main__':
    run()
# created on 2022-04-03
