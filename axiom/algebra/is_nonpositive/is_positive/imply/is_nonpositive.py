from util import *


@apply
def apply(is_nonpositive_y, is_positive_x):
    x = is_positive_x.of(Expr > 0)
    y = is_nonpositive_y.of(Expr <= 0)
    return LessEqual(x * y, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    Eq << apply(y <= 0, x > 0)

    Eq << algebra.is_positive.is_nonpositive.imply.is_nonpositive.apply(Eq[1], Eq[0])


if __name__ == '__main__':
    run()
