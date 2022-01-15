from util import *


@apply
def apply(given):
    S_abs, positive = given.of(GreaterEqual)
    assert positive.is_extended_positive
    S = S_abs.of(Card)

    x = S.element_symbol()

    return Unequal(S, S.etype.emptySet)


@prove
def prove(Eq):
    from axiom import algebra, sets

    S = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Card(S) >= 1)

    Eq << algebra.ge.imply.gt.relax.apply(Eq[0], 0)

    Eq << sets.gt_zero.imply.ne_empty.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-07-15
