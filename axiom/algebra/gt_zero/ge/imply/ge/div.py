from util import *


@apply
def apply(is_positive_x, ge):
    x = is_positive_x.of(Expr > 0)
    lhs, rhs = ge.of(GreaterEqual)
    return GreaterEqual(lhs / x, rhs / x)


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b = Symbol(real=True)
    Eq << apply(x > 0, a >= b)

    Eq << algebra.gt_zero.imply.gt_zero.div.apply(Eq[0])

    Eq << algebra.gt_zero.ge.imply.ge.mul.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2018-07-20
