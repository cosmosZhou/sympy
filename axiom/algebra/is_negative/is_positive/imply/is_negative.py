from util import *
import axiom



@apply
def apply(*given):
    is_negative_y, is_positive_x = given
    x = axiom.is_positive(is_positive_x)
    y = axiom.is_negative(is_negative_y)
    return Less(x * y, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    Eq << apply(y < 0, x > 0)

    Eq << -Eq[0]

    Eq << algebra.is_positive.is_positive.imply.is_positive.mul.apply(Eq[-1], Eq[1])

    Eq << -Eq[-1]


if __name__ == '__main__':
    run()