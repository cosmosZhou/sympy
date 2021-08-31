from util import *



@apply
def apply(x_imply_P, y_imply_P):
    x, p = x_imply_P.of(Suffice)
    y, q = y_imply_P.of(Suffice)

    return Suffice(x | y, p | q)


@prove
def prove(Eq):
    from axiom import algebra
    x, y, a, b = Symbol(real=True, given=True)

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
