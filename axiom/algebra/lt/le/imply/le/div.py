from util import *


@apply
def apply(lt, le):
    if le.is_Less:
        lt, le = le, lt
    x, y = lt.of(Less)
    x = y - x
    lhs, rhs = le.of(LessEqual)
    return LessEqual(lhs / x, rhs / x)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, a, b = Symbol(real=True)
    Eq << apply(x < y, a * (y - x) <= b)

    Eq << algebra.lt.imply.gt_zero.apply(Eq[0])

    Eq << algebra.gt_zero.le.imply.le.div.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2020-01-05
