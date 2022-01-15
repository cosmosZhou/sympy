from util import *


@apply
def apply(given):
    x, X = given.of(Element)

    return Equal(Card(X - {x}), Card(X) - 1)


@prove
def prove(Eq):
    from axiom import sets

    e = Symbol(integer=True)
    s = Symbol(etype=dtype.integer)
    Eq << apply(Element(e, s))

    Eq << sets.el.imply.subset.apply(Eq[0], simplify=False)

    Eq << sets.subset.imply.eq.union.apply(Eq[-1])

    Eq << sets.imply.eq.principle.add.apply(s, {e})

    Eq << Eq[-1].subs(Eq[-2]).reversed - 1


if __name__ == '__main__':
    run()
# created on 2021-03-07
