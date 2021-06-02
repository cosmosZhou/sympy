from util import *
import axiom



@apply
def apply(*given):
    is_nonnegative_x, is_positive_y = given
    x = axiom.is_nonnegative(is_nonnegative_x)
    y = axiom.is_positive(is_positive_y)
    return GreaterEqual(x * y, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    Eq << apply(x >= 0, y > 0)

    Eq << algebra.is_positive.is_nonnegative.imply.is_nonnegative.apply(Eq[1], Eq[0])


if __name__ == '__main__':
    run()
