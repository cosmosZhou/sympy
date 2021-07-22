from util import *


@apply
def apply(given):
    x, X = given.of(Contains)

    return Equal(abs(X - {x}), abs(X) - 1)


@prove
def prove(Eq):
    from axiom import sets

    e = Symbol.e(integer=True)
    s = Symbol.s(etype=dtype.integer)
    Eq << apply(Contains(e, s))

    Eq << sets.contains.imply.subset.apply(Eq[0], simplify=False)

    Eq << sets.subset.imply.eq.union.apply(Eq[-1])

    Eq << sets.imply.eq.principle.addition.apply(s, {e})

    Eq << Eq[-1].subs(Eq[-2]).reversed - 1


if __name__ == '__main__':
    run()