from util import *


@apply
def apply(given):
    e, S = given.of(NotElement)
    return Equal(Card(S | {e}), Card(S) + 1)


@prove
def prove(Eq):
    from axiom import sets

    S = Symbol(etype=dtype.integer)
    e = Symbol(integer=True)
    Eq << apply(NotElement(e, S))

    Eq << sets.notin.imply.is_empty.intersect.apply(Eq[0])

    Eq << sets.intersect_is_empty.imply.eq.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-03-17
# updated on 2021-03-17
