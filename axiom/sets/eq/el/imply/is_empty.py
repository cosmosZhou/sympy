from util import *


@apply
def apply(equal, contains):
    if contains.is_Equal:
        contains, equal = equal, contains

    a, A = contains.of(Element)

    _A = equal.of(Equal[Card, 1])
    assert _A == A
    return Equal(A - a.set, a.emptySet)


@prove
def prove(Eq):
    from axiom import sets

    A = Symbol(etype=dtype.integer, given=True)
    a = Symbol(integer=True, given=True)
    Eq << apply(Equal(Card(A), 1), Element(a, A))

    Eq << sets.eq.el.imply.eq.finiteset.apply(Eq[0], Eq[1])

    Eq << sets.eq.imply.eq.complement.apply(Eq[-1], a.set)


if __name__ == '__main__':
    run()
# created on 2021-03-16
# updated on 2021-03-16
