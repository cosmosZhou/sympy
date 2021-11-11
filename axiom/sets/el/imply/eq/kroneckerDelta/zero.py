from util import *


@apply
def apply(given):
    x, domain = given.of(Element)
    assert domain == FiniteSet(0, 1)

    return Equal(KroneckerDelta(0, x), 1 - x)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol(integer=True, given=True)
    given = Element(x, {0, 1})
    Eq << apply(given)

    Eq << Eq[-1].this.lhs.apply(algebra.kroneckerDelta.to.piece)

    Eq << Eq[-1].apply(algebra.cond.given.et.ou, cond=Equal(x, 0))

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq <<= ~Eq[-1], ~Eq[-2]

    Eq << Eq[-2].apply(algebra.eq.ne.imply.ne.subs)

    Eq << Eq[-1].apply(algebra.cond.cond.imply.cond.subs, invert=True, reverse=True, swap=True, ret=1)

    Eq << Eq[-1].apply(sets.ne.ne.imply.notin, simplify=False)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2020-08-29
# updated on 2020-08-29
