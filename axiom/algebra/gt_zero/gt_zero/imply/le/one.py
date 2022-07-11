from util import *


@apply
def apply(gt_zero_a, gt_zero_b):
    a = gt_zero_a.of(ReducedSum[Expr ** 2] > 0)
    b = gt_zero_b.of(ReducedSum[Expr ** 2] > 0)
    return abs(ReducedSum(a * b)) / (sqrt(ReducedSum(a ** 2)) * sqrt(ReducedSum(b ** 2))) <= 1


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(domain=Range(2, oo))
    a, b = Symbol(shape=(n,), real=True, given=True)
    Eq << apply(ReducedSum(a ** 2) > 0, ReducedSum(b ** 2) > 0)

    Eq << ~Eq[-1]

    Eq << algebra.gt_zero.imply.gt_zero.sqrt.apply(Eq[0] * Eq[1])

    Eq << algebra.gt_zero.gt.imply.gt.mul.apply(Eq[-1], Eq[-2])

    Eq << algebra.gt_zero.gt.imply.gt.square.apply(Eq[-2], Eq[-1])

    Eq << algebra.imply.le.Cauchy.apply(a, b)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2022-04-02
