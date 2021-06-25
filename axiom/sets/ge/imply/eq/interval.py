from util import *


@apply
def apply(given, left_open=False, right_open=False):
    a, b = given.of(GreaterEqual)
    if left_open or right_open:
        rhs = a.emptySet
    else:
        rhs = a.set & b.set
    return Equal(Interval(a, b, left_open=left_open, right_open=right_open), rhs)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    Eq << apply(x >= y)

    Eq << algebra.cond.given.suffice.split.apply(Eq[-1], cond=x > y)

    Eq.is_zero = (x > y).this.apply(sets.gt.imply.eq.emptySet)

    Eq << sets.imply.subset.intersection.apply(x, y)

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
