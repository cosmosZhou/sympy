from util import *


@apply
def apply(given):
    x, RR = given.of(Contains)
    RR |= {0}

    assert RR.is_UniversalSet
    return Greater(abs(x), 0)


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(complex=True)
    Eq << apply(Contains(x, Reals - {0}))

    Eq << sets.contains.imply.ou.split.union.apply(Eq[0], simplify=False)

    Eq.is_negative = Suffice(Eq[-1].args[0], Eq[1], plausible=True)

    Eq << Eq.is_negative.this.lhs.apply(sets.contains.imply.is_negative)

    Eq << Eq[-1].this.lhs.apply(algebra.is_negative.imply.is_nonzero)

    Eq << Eq[-1].this.lhs.apply(algebra.is_nonzero.imply.abs_is_positive)

    Eq.is_positive = Suffice(Eq[2].args[1], Eq[1], plausible=True)

    Eq << Eq.is_positive.this.lhs.apply(sets.contains.imply.is_positive)

    Eq << Eq[-1].this.lhs.apply(algebra.is_positive.imply.is_nonzero)

    Eq << algebra.suffice.suffice.imply.suffice.ou.apply(Eq.is_negative, Eq.is_positive)

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

