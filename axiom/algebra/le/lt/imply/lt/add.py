from util import *
import axiom



@apply
def apply(*given):
    a_less_than_x, x_less_than_b = given
    a, x = a_less_than_x.of(LessEqual)
    b, y = x_less_than_b.of(Less)

    return Less(a + b, x + y)


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)
    y = Symbol.y(real=True)

    Eq << apply(a <= x, y < b)

    Eq << Eq[0] + y

    Eq << Eq[1] + x

    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[-2], Eq[-1])



if __name__ == '__main__':
    run()
