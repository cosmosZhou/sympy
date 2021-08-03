from util import *


@apply
def apply(given):
    x, domain = given.of(Contains)
    assert domain == FiniteSet(0, 1)

    return Equal(KroneckerDelta(1, x), x)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol.x(integer=True, given=True)
    given = Contains(x, {0, 1})
    Eq << apply(given)

    Eq << Eq[-1].this.lhs.apply(algebra.kroneckerDelta.to.piecewise)

    Eq << Eq[-1].apply(algebra.cond.given.et.ou, cond=Equal(1, x))

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq <<= ~Eq[-1], ~Eq[-2]

    Eq << Eq[-2].apply(algebra.eq.ne.imply.ne.subs)

    Eq << Eq[-1].apply(algebra.et.imply.et.invoke, algebra.cond.cond.imply.cond.subs, invert=True)

    Eq << Eq[-1].apply(sets.ne.ne.imply.notcontains, simplify=False)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

