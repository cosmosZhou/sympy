from util import *


@apply
def apply(given):
    abs_S, size = given.of(Greater)
    assert size.is_extended_nonnegative
    S = abs_S.of(Card)
    x = S.element_symbol()
    return Any[x](Element(x, S))


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol(etype=dtype.integer)
    Eq << apply(Card(A) > 0)

    Eq << sets.gt_zero.imply.ne_empty.apply(Eq[0])

    Eq << sets.ne_empty.imply.any_el.apply(Eq[-1], simplify=False)


if __name__ == '__main__':
    run()

# created on 2020-07-13
