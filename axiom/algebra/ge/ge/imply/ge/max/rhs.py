from util import *
import axiom



@apply
def apply(*given):
    x_less_than_y, x_less_than_b = given
    x, y = x_less_than_y.of(GreaterEqual)
    _x, b = x_less_than_b.of(GreaterEqual)
    assert x == _x
    return GreaterEqual(x, Max(y, b))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)

    b = Symbol.b(real=True, given=True)

    Eq << apply(x >= y, x >= b)

    Eq << Eq[-1].this.rhs.astype(Piecewise)

    Eq << algebra.cond.given.ou.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << algebra.cond.cond.imply.cond.apply(Eq[0], Eq[-1], invert=True, reverse=True)

    Eq << algebra.cond.cond.imply.cond.apply(Eq[1], Eq[-1], invert=True, reverse=True)

if __name__ == '__main__':
    run()
