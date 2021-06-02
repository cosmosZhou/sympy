from util import *


@apply
def apply(given):
    assert given.is_Contains
    x, domain = given.args
    assert domain == FiniteSet(0, 1)

    return Equal(KroneckerDelta(0, x), 1 - x)


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(integer=True, given=True)
    given = Contains(x, {0, 1})

    Eq << apply(given)

    Eq << Eq[-1].this.lhs.astype(Piecewise)

    Eq << Eq[-1].apply(algebra.cond.given.et.ou, cond=Equal(x, 0))

    Eq << algebra.et.given.conds.apply(Eq[-1])

    Eq <<= ~Eq[-1], ~Eq[-2]

    Eq << Eq[-2].apply(algebra.eq.ne.imply.ne.subs)

    Eq << Eq[-1].apply(algebra.cond.cond.imply.et, invert=True, reverse=True, swap=True)

    Eq << Eq[-1].apply(sets.ne.ne.imply.notcontains, simplify=False)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()