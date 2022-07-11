from util import *


@apply
def apply(ou, inter0, inter1):
    p0, p1 = ou.of(Or)
    S[p0], q0 = inter0.of(Infer)
    S[p1], q1 = inter1.of(Infer)

    return p0 & q0 | p1 & q1


@prove
def prove(Eq):
    from axiom import algebra

    p0, q0, p1, q1 = Symbol(bool=True)
    Eq << apply(p0 | p1, p0 >> q0, p1 >> q1)

    Eq << ~Eq[-1]

    Eq << algebra.infer.imply.ou.apply(Eq[1])

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.apply(algebra.et.to.ou)

    Eq << Eq[-1].this.args[0].apply(algebra.et.to.ou)

    Eq << algebra.infer.imply.ou.apply(Eq[2])

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.apply(algebra.et.to.ou)

    Eq << Eq[-1].this.args[0].apply(algebra.et.to.ou)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2022-04-01
