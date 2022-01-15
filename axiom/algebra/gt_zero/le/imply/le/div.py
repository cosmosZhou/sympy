from util import *


@apply
def apply(is_positive_x, less_than):
    x = is_positive_x.of(Expr > 0)
    lhs, rhs = less_than.of(LessEqual)
    return LessEqual(lhs / x, rhs / x)


@prove
def prove(Eq):
    from axiom import algebra
    x, a, b = Symbol(real=True)

    Eq << apply(x > 0, a <= b)


    Eq << algebra.gt_zero.imply.gt_zero.div.apply(Eq[0])

    Eq << algebra.gt_zero.le.imply.le.mul.apply(Eq[-1], Eq[1])




if __name__ == '__main__':
    run()
# created on 2019-07-31
