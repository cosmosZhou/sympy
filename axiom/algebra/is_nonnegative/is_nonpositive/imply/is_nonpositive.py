from util import *
import axiom



@apply
def apply(*given):
    is_nonnegative, is_nonpositive_y = given
    x = axiom.is_nonnegative(is_nonnegative)
    y = axiom.is_nonpositive(is_nonpositive_y)
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