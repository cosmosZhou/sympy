from util import *
import axiom



@apply
def apply(*given):
    b_greater_than_x, x_greater_than_a = given
    b, x = b_greater_than_x.of(Greater)
    _x, a = x_greater_than_a.of(Greater)
    assert x == _x
    return Less(a, b)


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(b > x, x > a)

    Eq << algebra.gt.gt.imply.gt.transit.apply(Eq[0], Eq[1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
