from util import *



@apply
def apply(x_less_than_y, a_less_than_b):
    x, y = x_less_than_y.of(Greater)
    a, b = a_less_than_b.of(Greater)
    return Greater(Max(x, a), Max(y, b))


@prove
def prove(Eq):
    from axiom import algebra
    x, y, a, b = Symbol(real=True)


    Eq << apply(x > y, a > b)

    Eq << GreaterEqual(Max(x, a), x, plausible=True)

    Eq << algebra.ge.gt.imply.gt.transit.apply(Eq[-1], Eq[0])

    Eq << GreaterEqual(Max(x, a), a, plausible=True)

    Eq << algebra.gt.ge.imply.gt.transit.apply(Eq[1], Eq[-1])

    Eq << algebra.gt.gt.imply.gt.max.rhs.apply(Eq[-1], Eq[-3])

if __name__ == '__main__':
    run()
# created on 2019-03-09
# updated on 2019-03-09
