from util import *


@apply
def apply(given):
    x_union_abs, x_abs_sum = given.of(Equal)
    if not x_union_abs.is_Abs:
        tmp = x_union_abs
        x_union_abs = x_abs_sum
        x_abs_sum = tmp
        assert x_union_abs.is_Abs

    x_union = x_union_abs.arg
    assert x_union.is_Union
    A, B = x_union.args

    assert x_abs_sum.is_Add
    A_abs, B_abs = x_abs_sum.args
    assert A_abs.is_Abs
    assert B_abs.is_Abs
    _A = A_abs.arg
    _B = B_abs.arg

    assert {A, B} == {_A, _B}

    return Equal(A & B, A.etype.emptySet)


@prove
def prove(Eq):
    from axiom import sets, algebra
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)

    Eq << apply(Equal(abs(A | B), abs(A) + abs(B)))

    Eq << sets.imply.eq.principle.inclusion_exclusion.basic.apply(A, B)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.apply(algebra.eq.simplify.terms.common)

    Eq << -Eq[-1]

    Eq << Eq[-1].apply(sets.is_zero.imply.is_emptyset)


if __name__ == '__main__':
    run()

