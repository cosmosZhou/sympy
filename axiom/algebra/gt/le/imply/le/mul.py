from util import *


@apply
def apply(gt, le):
    a, b = gt.of(Greater)
    x, y = le.of(LessEqual)
    z = a - b
    return LessEqual(z * x,  z * y)


@prove
def prove(Eq):
    from axiom import algebra
    a, b, x, y = Symbol(real=True)
    Eq << apply(a > b, x <= y)

    Eq << algebra.gt.imply.gt_zero.apply(Eq[0])

    Eq << algebra.gt_zero.le.imply.le.mul.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-08-01
