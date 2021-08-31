from util import *


@apply
def apply(gt, le):
    if le.is_Greater:
        gt, le = le, gt
    x, y = gt.of(Greater)
    z = x - y
    lhs, rhs = le.of(LessEqual)
    return LessEqual(lhs / z, rhs / z)


@prove
def prove(Eq):
    from axiom import algebra
    x, y, a, b = Symbol(real=True)
    Eq << apply(x > y, a * (y - x) <= b)

    Eq << algebra.gt.imply.is_positive.apply(Eq[0])

    Eq << algebra.is_positive.le.imply.le.div.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
