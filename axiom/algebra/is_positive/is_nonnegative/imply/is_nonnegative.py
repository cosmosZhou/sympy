from util import *


@apply
def apply(is_positive_x, is_nonnegative_y):
    x = is_positive_x.of(Expr > 0)
    y = is_nonnegative_y.of(Expr >= 0)
    return GreaterEqual(x * y, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True)

    Eq << apply(x > 0, y >= 0)

    Eq << -algebra.is_positive.is_nonpositive.imply.is_nonpositive.apply(Eq[0], -Eq[1])


if __name__ == '__main__':
    run()
