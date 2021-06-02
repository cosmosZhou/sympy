from util import *
import axiom



@apply
def apply(*given):
    a_less_than_x, x_less_than_b = given
    a, x = a_less_than_x.of(Less)
    _x, b = x_less_than_b.of(LessEqual)
    if x != _x:
        a, x, _x, b = _x, b, a, x
    assert x == _x
    return Less(a, b)


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol.a(real=True, given=True)
    x = Symbol.x(real=True, given=True)
    b = Symbol.b(real=True, given=True)

    Eq << apply(a < x, x <= b)

    Eq << ~Eq[2]

    Eq << algebra.ge.le.imply.ge.transit.apply(Eq[-1], Eq[1])

    Eq <<= Eq[0] & Eq[-1]


if __name__ == '__main__':
    run()
