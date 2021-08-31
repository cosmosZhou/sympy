from util import *


@apply
def apply(is_nonnegative, ge):
    if 0 not in is_nonnegative.args:
        ge, is_nonnegative = given

    x = is_nonnegative.of(Expr >= 0)
    a, b = ge.of(Greater)
    return GreaterEqual(a * x, b * x)


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b = Symbol(real=True)
    Eq << apply(x >= 0, a > b)

    Eq << Eq[1] - b

    Eq << algebra.is_nonnegative.is_positive.imply.is_nonnegative.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << algebra.is_nonnegative.imply.ge.apply(Eq[-1])


if __name__ == '__main__':
    run()

