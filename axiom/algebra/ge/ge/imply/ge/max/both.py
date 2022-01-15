from util import *



@apply
def apply(x_less_than_y, a_less_than_b):
    x, y = x_less_than_y.of(GreaterEqual)
    a, b = a_less_than_b.of(GreaterEqual)
    return GreaterEqual(Max(x, a), Max(y, b))


@prove
def prove(Eq):
    from axiom import algebra
    x, y, a, b = Symbol(real=True)


    Eq << apply(x >= y, a >= b)

    Eq << GreaterEqual(Max(x, a), x, plausible=True)

    Eq << algebra.ge.ge.imply.ge.transit.apply(Eq[-1], Eq[0])

    Eq << GreaterEqual(Max(x, a), a, plausible=True)

    Eq << algebra.ge.ge.imply.ge.transit.apply(Eq[1], Eq[-1])

    Eq << algebra.ge.ge.imply.ge.max.rhs.apply(Eq[-1], Eq[-3])

if __name__ == '__main__':
    run()
# created on 2019-05-17
