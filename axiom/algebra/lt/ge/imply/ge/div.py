from util import *


@apply
def apply(lt, ge):
    if ge.is_Less:
        lt, ge = ge, lt
    x, y = lt.of(Less)
    x = y - x
    lhs, rhs = ge.of(GreaterEqual)
    return GreaterEqual(lhs / x, rhs / x)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, a, b = Symbol(real=True)
    Eq << apply(x < y, a * (y - x) >= b)

    Eq << algebra.lt.imply.gt_zero.apply(Eq[0])

    Eq << algebra.gt_zero.ge.imply.ge.div.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-12-13
