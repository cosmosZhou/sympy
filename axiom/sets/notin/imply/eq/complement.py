from util import *


# given e not in S


# => S - {e} = S
@apply
def apply(given):
    e, S = given.of(NotElement)
    return Equal(S - {e}, S)


@prove
def prove(Eq):
    from axiom import sets

    S = Symbol(etype=dtype.integer)
    e = Symbol(integer=True)
    Eq << apply(NotElement(e, S))

    Eq << sets.notin.imply.is_empty.intersect.apply(Eq[0])

    Eq << sets.intersect_is_empty.imply.eq.complement.apply(Eq[-1])


if __name__ == '__main__':
    run()

