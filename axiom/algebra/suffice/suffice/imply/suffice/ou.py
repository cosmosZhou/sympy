from util import *
import axiom



@apply
def apply(*given):
    x_imply_P, y_imply_P = given
    x, p = x_imply_P.of(Suffice)
    y, q = y_imply_P.of(Suffice)

    return Suffice(x | y, p | q)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)

    Eq << apply(Suffice(x > 0, a > 0), Suffice(y > 0, b > 0))

    Eq << Eq[-1].apply(algebra.suffice.given.ou)

    Eq << ~Eq[-1]

    Eq << Eq[0].apply(algebra.suffice.imply.ou)

    Eq <<= Eq[-2] & Eq[-1]

    Eq << algebra.et.imply.ou.apply(Eq[-1])

    Eq << Eq[1].apply(algebra.suffice.imply.ou)

    Eq <<= Eq[-2] & Eq[-1]







if __name__ == '__main__':
    run()
