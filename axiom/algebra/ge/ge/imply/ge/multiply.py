from util import *
import axiom



@apply
def apply(*given):
    a_less_than_b, x_less_than_y = given
    a, b = a_less_than_b.of(GreaterEqual)
    x, y = x_less_than_y.of(GreaterEqual)

    assert b.is_nonnegative
    assert y.is_nonnegative
    return GreaterEqual(a * x, b * y)


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True, nonnegative=True)
    y = Symbol.y(real=True, nonnegative=True)

    Eq << apply(a >= b, x >= y)

    Eq << algebra.le.le.imply.le.multiply.apply(Eq[0].reversed, Eq[1].reversed)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
