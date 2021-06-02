from util import *
import axiom



@apply
def apply(*given):
    x_less_than_y, a_less_than_b = given
    x, y = x_less_than_y.of(Less)
    a, b = a_less_than_b.of(Less)
    return Less(Min(x, a), Min(y, b))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    Eq << apply(x < y, a < b)

    Eq << LessEqual(Min(x, a), x, plausible=True)

    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[-1], Eq[0])

    Eq << LessEqual(Min(x, a), a, plausible=True)

    Eq << algebra.lt.le.imply.lt.transit.apply(Eq[1], Eq[-1])

    Eq << algebra.lt.lt.imply.lt.min.apply(Eq[-1], Eq[-3])

if __name__ == '__main__':
    run()
