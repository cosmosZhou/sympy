from util import *



@apply
def apply(x_less_than_1, y_less_than_1):
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

    x, y = Symbol(real=True, nonnegative=True)
    Eq << apply(x <= 1, y <= 1)

    Eq.is_nonpositive = Eq[-1] - Eq[-1].rhs

    Eq << GreaterEqual(x, 0, plausible=True)

    Eq.le = algebra.le.ge.imply.le.quadratic.apply(Eq[-1], Eq[0], quadratic=Eq.is_nonpositive.lhs)

    Eq << GreaterEqual(y, 0, plausible=True)

    Eq << algebra.le.ge.imply.le.quadratic.apply(Eq[-1], Eq[1], quadratic=Eq.le.rhs.args[0])

    Eq << algebra.le.ge.imply.le.quadratic.apply(Eq[-2], Eq[1], quadratic=Eq.le.rhs.args[1])

    Eq << algebra.le.le.imply.le.max.apply(Eq[-1], Eq[-2])

    Eq << algebra.le.le.imply.le.transit.apply(Eq[-1], Eq.le)


if __name__ == '__main__':
    run()
