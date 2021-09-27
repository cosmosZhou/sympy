from util import *


@apply
def apply(given):
    x_union_abs, x_abs_sum = given.of(Equal)
    if not x_union_abs.is_Card:
        tmp = x_union_abs
        x_union_abs = x_abs_sum
        x_abs_sum = tmp
        assert x_union_abs.is_Card

    x_union = x_union_abs.arg
    assert x_union.is_Union
    A, B = x_union.args

    assert x_abs_sum.is_Add
    A_abs, B_abs = x_abs_sum.args
    _A = A_abs.of(Card)
    _B = B_abs.of(Card)

    assert {A, B} == {_A, _B}

    return Equal(A & B, A.etype.emptySet)


@prove
def prove(Eq):
    from axiom import sets, algebra

    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Equal(Card(A | B), Card(A) + Card(B)))

    Eq << sets.imply.eq.principle.inclusion_exclusion.basic.apply(A, B)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.apply(algebra.eq.simplify.terms.common)

    Eq << -Eq[-1]

    Eq << Eq[-1].apply(sets.is_zero.imply.is_empty)


if __name__ == '__main__':
    run()

