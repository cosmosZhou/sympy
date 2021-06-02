from util import *
import axiom



@apply
def apply(*given):
    is_positive_x, strict_greater_than = given
    x = axiom.is_positive(is_positive_x)
    lhs, rhs = strict_greater_than.of(Greater)
    return Greater(lhs * x, rhs * x)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    Eq << apply(x > 0, a > b)

    Eq << Eq[1] - b

    Eq << algebra.is_positive.is_positive.imply.is_positive.mul.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1] + b * x


if __name__ == '__main__':
    run()
