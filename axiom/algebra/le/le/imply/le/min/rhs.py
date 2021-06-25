from util import *


@apply
def apply(x_less_than_y, x_less_than_b):
    x, y = x_less_than_y.of(LessEqual)
    _x, b = x_less_than_b.of(LessEqual)
    assert x == _x
    return LessEqual(x, Min(y, b))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)

    b = Symbol.b(real=True, given=True)

    Eq << apply(x <= y, x <= b)

    Eq << Eq[-1].this.rhs.apply(algebra.min.to.piecewise)

    Eq << algebra.cond.given.ou.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << algebra.cond.cond.imply.cond.apply(Eq[0], Eq[-1], invert=True, reverse=True)

    Eq << algebra.cond.cond.imply.cond.apply(Eq[1], Eq[-1], invert=True, reverse=True)


if __name__ == '__main__':
    run()
