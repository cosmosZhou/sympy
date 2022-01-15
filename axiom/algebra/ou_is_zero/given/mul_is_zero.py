from util import *


@apply
def apply(given):
    eqs = given.of(Or)

    args = []
    for eq in eqs:
        args.append(eq.of(Equal[0]))

    return Equal(Mul(*args), 0)


@prove
def prove(Eq):
    from axiom import algebra

    a, b = Symbol(real=True, given=True)
    Eq << apply(Equal(a, 0) | Equal(b, 0))

    Eq << ~Eq[0]

    Eq <<= Eq[-1] & Eq[1]

    Eq << Equivalent(Equal(Bool(Unequal(a, 0) & Equal(a * b, 0)), 1) & Unequal(b, 0),
                     Eq[-1], plausible=True)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << Equivalent(Unequal(a, 0) & Equal(a * b, 0),
                     Unequal(a, 0) & Equal(b, 0), plausible=True)

    Eq << algebra.iff.given.et.infer.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(algebra.ne_zero.eq.imply.eq.div)

    Eq << Eq[-1].this.lhs.apply(algebra.ne_zero.eq.imply.eq.mul)

    Eq << algebra.iff.imply.eq.apply(Eq[-3])

    Eq << Eq[4].subs(Eq[-1])

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << Eq[-1].subs(Eq[1])


if __name__ == '__main__':
    run()

# created on 2018-01-29
