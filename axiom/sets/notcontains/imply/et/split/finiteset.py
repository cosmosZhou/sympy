from util import *


@apply
def apply(given):
    e, S = given.of(NotContains)
    args = S.of(FiniteSet)

    eqs = [Unequal(e, s) for s in args]

    return And(*eqs)


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)

    Eq << apply(NotContains(x, {a, b}))

    Eq << algebra.et.given.conds.apply(Eq[1])

    Eq << sets.notcontains.imply.ne.apply(Eq[0])

    Eq << sets.notcontains.imply.ne.apply(Eq[0], index=1)


if __name__ == '__main__':
    run()

