from util import *
import axiom



@apply
def apply(*given):
    is_negative_x, is_negative_y = given
    x = axiom.is_negative(is_negative_x)
    y = axiom.is_negative(is_negative_y)
    return Greater(x * y, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    Eq << apply(x < 0, y < 0)

    Eq << algebra.is_positive.is_positive.imply.is_positive.mul.apply(-Eq[0], -Eq[1])


if __name__ == '__main__':
    run()
