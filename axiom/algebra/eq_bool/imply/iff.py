from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    lhs = lhs.of(Bool)
    rhs = rhs.of(Bool)
    return Equivalent(lhs, rhs)


@prove
def prove(Eq):
    from axiom import algebra
    a, b = Symbol(integer=True)
    f = Function(shape=())

    Eq << apply(Equal(Bool(a > b), Bool(f(a) > f(b))))

    Eq << Eq[0] * Eq[0].lhs

    Eq << algebra.pow.to.bool.apply(Eq[-1].lhs)

    Eq << Eq[-2] - Eq[-1]

    Eq << algebra.is_zero.imply.eq.apply(Eq[-1])

    Eq.suffice = algebra.eq.imply.infer.bool.apply(Eq[-1])

    Eq << Eq[0] * Eq[0].rhs

    Eq << algebra.pow.to.bool.apply(Eq[0].rhs ** 2)

    Eq << Eq[-2] + Eq[-1]

    Eq << Eq[-1].this.apply(algebra.eq.simplify.terms.common)

    Eq << algebra.eq.imply.infer.bool.apply(Eq[-1])

    Eq <<= Eq.suffice & Eq[-1]


if __name__ == '__main__':
    run()

# created on 2018-03-22
