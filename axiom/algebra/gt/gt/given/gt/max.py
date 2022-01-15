from util import *


@apply
def apply(gt_a, gt_b):
    x, a = gt_a.of(Greater)
    S[x], b = gt_b.of(Greater)
    return x > Max(a, b)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, b = Symbol(real=True, given=True)
    Eq << apply(x > y, x > b)

    Eq << algebra.gt_max.imply.et.gt.apply(Eq[2])


if __name__ == '__main__':
    run()
# created on 2022-01-03
