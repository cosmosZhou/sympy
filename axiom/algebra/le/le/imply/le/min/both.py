from util import *



@apply
def apply(*given):
    x_less_than_y, a_less_than_b = given
    x, y = x_less_than_y.of(LessEqual)
    a, b = a_less_than_b.of(LessEqual)
    return LessEqual(Min(x, a), Min(y, b))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    Eq << apply(x <= y, a <= b)

    Eq << LessEqual(Min(x, a), x, plausible=True)

    Eq << algebra.le.le.imply.le.transit.apply(Eq[-1], Eq[0])

    Eq << LessEqual(Min(x, a), a, plausible=True)

    Eq << algebra.le.le.imply.le.transit.apply(Eq[1], Eq[-1])

    Eq << algebra.le.le.imply.le.min.rhs.apply(Eq[-1], Eq[-3])

if __name__ == '__main__':
    run()
