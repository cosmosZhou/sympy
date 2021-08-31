from util import *


@apply
def apply(is_positive_x, less_than):
    x = is_positive_x.of(Expr > 0)
    lhs, rhs = less_than.of(LessEqual)
    return LessEqual(lhs * x, rhs * x)


@prove
def prove(Eq):
    from axiom import algebra
    x, a, b = Symbol(real=True)

    Eq << apply(x > 0, a <= b)

    Eq << Eq[1] - b

    Eq << algebra.is_positive.is_nonpositive.imply.is_nonpositive.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1] + b * x


if __name__ == '__main__':
    run()
