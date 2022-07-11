from util import *



@apply
def apply(x_imply_P, y_imply_P):
    x, p = x_imply_P.of(Infer)
    y, q = y_imply_P.of(Infer)

    return Infer(x | y, p | q)


@prove
def prove(Eq):
    from axiom import algebra

    p0, p1, q0, q1 = Symbol(bool=True)
    Eq << apply(Infer(p0, q0), Infer(p1, q1))

    Eq << Eq[-1].apply(algebra.infer.given.ou)

    Eq << ~Eq[-1]

    Eq << Eq[0].apply(algebra.infer.imply.ou)

    Eq <<= Eq[-2] & Eq[-1]

    Eq << algebra.et.imply.ou.apply(Eq[-1])

    Eq << Eq[1].apply(algebra.infer.imply.ou)

    Eq <<= Eq[-2] & Eq[-1]

    


if __name__ == '__main__':
    run()
# created on 2018-02-09
# updated on 2022-01-27
