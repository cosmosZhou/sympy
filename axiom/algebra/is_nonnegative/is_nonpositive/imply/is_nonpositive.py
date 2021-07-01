from util import *


@apply
def apply(is_nonnegative, is_nonpositive_y):
    x = is_nonnegative.of(Expr >= 0)
    y = is_nonpositive_y.of(Expr <= 0)
    return LessEqual(x * y, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    Eq << apply(x >= 0, y <= 0)

    Eq << algebra.is_nonpositive.is_nonnegative.imply.is_nonpositive.apply(Eq[1], Eq[0])


if __name__ == '__main__':
    run()
