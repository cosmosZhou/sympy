from util import *


@apply
def apply(is_nonpositive_x, is_nonpositive_y):
    x = is_nonpositive_x.of(Expr <= 0)
    y = is_nonpositive_y.of(Expr <= 0)
    return GreaterEqual(x * y, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    Eq << apply(x <= 0, y <= 0)

    Eq << algebra.is_nonnegative.is_nonnegative.imply.is_nonnegative.apply(-Eq[0], -Eq[1])


if __name__ == '__main__':
    run()
