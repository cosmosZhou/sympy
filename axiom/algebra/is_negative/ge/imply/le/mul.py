from util import *


@apply
def apply(is_negative, ge):
    x = is_negative.of(Expr < 0)
    #assert x.is_finite
    lhs, rhs = ge.of(GreaterEqual)
    return LessEqual(lhs * x, rhs * x)


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b = Symbol(real=True)
    Eq << apply(x < 0, a >= b)

    Eq << Eq[1] - b

    Eq << algebra.is_negative.is_nonnegative.imply.is_nonpositive.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1] + b * x


if __name__ == '__main__':
    run()
