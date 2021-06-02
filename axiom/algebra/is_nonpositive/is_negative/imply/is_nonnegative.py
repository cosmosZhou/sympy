from util import *
import axiom



@apply
def apply(*given):
    is_nonpositive_x, is_negative_y = given
    x = axiom.is_nonpositive(is_nonpositive_x)
    y = axiom.is_negative(is_negative_y)
    return GreaterEqual(x * y, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    Eq << apply(x <= 0, y < 0)

    Eq << algebra.is_negative.is_nonpositive.imply.is_nonnegative.apply(Eq[1], Eq[0])

if __name__ == '__main__':
    run()
