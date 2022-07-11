from util import *


@apply
def apply(gt_zero, add_gt_zero, x=None):
    a = gt_zero.of(Expr > 0)
    b, (S[a], c) = add_gt_zero.of(Expr ** 2 - 4 * Expr * Expr > 0)
    assert x.is_real
    assert a.is_real and b.is_real and c.is_real
    return Any[x](a * x ** 2 + b * x + c < 0)


@prove
def prove(Eq):
    from axiom import algebra

    a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(a > 0, b ** 2 - 4 * a * c > 0, x=x)

    Eq << algebra.gt_zero.imply.gt_zero.div.apply(Eq[0])

    Eq << algebra.any.given.cond.subs.apply(Eq[2], x, -Eq[-1].lhs * b / 2)

    Eq << algebra.gt_zero.gt_zero.imply.gt_zero.apply(Eq[-2], Eq[1])

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add)

    Eq << -Eq[-1] / 4


if __name__ == '__main__':
    run()
# created on 2022-04-03
