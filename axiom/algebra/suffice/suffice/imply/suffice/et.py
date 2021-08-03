from util import *



@apply
def apply(*given):
    is_imply_P, is_imply_Q = given
    x, p = is_imply_P.of(Suffice)
    y, q = is_imply_Q.of(Suffice)

    return Suffice(x & y, p & q)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(Suffice(x > 0, a > 0), Suffice(y > 0, b > 0))

    Eq << algebra.suffice.given.et.suffice.apply(Eq[-1])

    Eq <<= Suffice((x > 0) & (y > 0), x > 0, plausible=True), Suffice((x > 0) & (y > 0), y > 0, plausible=True)

    Eq <<= algebra.suffice.suffice.imply.suffice.transit.apply(Eq[0], Eq[-2]), algebra.suffice.suffice.imply.suffice.transit.apply(Eq[1], Eq[-1])


if __name__ == '__main__':
    run()
