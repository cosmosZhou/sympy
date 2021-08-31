from util import *


@apply
def apply(given):
    a, b = given.of(GreaterEqual)
    return Equal(Interval(a, b), a.set & b.set)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, y = Symbol(real=True, given=True)
    Eq << apply(x >= y)

    Eq << algebra.cond.given.et.suffice.split.apply(Eq[-1], cond=x > y)

    Eq.is_zero = (x > y).this.apply(sets.gt.imply.interval_is_empty)

    Eq << sets.imply.subset.intersect.apply(x, y)

    Eq << algebra.cond.suffice.imply.suffice.et.rhs.apply(Eq[-1], Eq.is_zero)

    Eq << Eq[-1].this.rhs.apply(algebra.eq.cond.imply.cond.subs)

    Eq << Eq[-1].this.rhs.apply(sets.subset.imply.eq.emptySet, simplify=None)

    Eq <<= Eq[-1] & Eq.is_zero

    Eq << Eq[-1].this.rhs.apply(algebra.eq.eq.imply.eq.transit)

    Eq << Suffice(x <= y, Equal(x, y), plausible=True)

    Eq << algebra.suffice.given.ou.apply(Eq[-1])

    Eq <<= Eq[3] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.et.given.et.subs.eq, index=1)


if __name__ == '__main__':
    run()
