from util import *

import axiom


@apply
def apply(*given):
    x_less_than_1, y_less_than_1 = given
    x, one = x_less_than_1.of(LessEqual)
    assert one.is_One
    y, one = y_less_than_1.of(LessEqual)
    assert one.is_One

    assert x >= 0
    assert y >= 0
    return LessEqual(x * x + y * y - 1, x * y)




@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, nonnegative=True)
    y = Symbol.y(real=True, nonnegative=True)

    Eq << apply(x <= 1, y <= 1)

    Eq.is_nonpositive = Eq[-1] - Eq[-1].rhs

    Eq << GreaterEqual(x, 0, plausible=True)

    Eq.le = algebra.ge.le.imply.le.quadratic.apply(Eq[-1], Eq[0], quadratic=Eq.is_nonpositive.lhs)

    Eq << GreaterEqual(y, 0, plausible=True)

    Eq << algebra.ge.le.imply.le.quadratic.apply(Eq[-1], Eq[1], quadratic=Eq.le.rhs.args[0])

    Eq << algebra.ge.le.imply.le.quadratic.apply(Eq[-2], Eq[1], quadratic=Eq.le.rhs.args[1])

    Eq << algebra.le.le.imply.le.max.apply(Eq[-1], Eq[-2])

    Eq << algebra.le.le.imply.le.transit.apply(Eq[-1], Eq.le)



if __name__ == '__main__':
    run()
