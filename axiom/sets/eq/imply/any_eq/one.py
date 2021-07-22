from util import *


@apply
def apply(given, reverse=False):
    S_abs, n = given.of(Equal)

    assert S_abs.is_Abs and n.is_extended_positive
    S = S_abs.arg
    x = S.element_symbol()
    if reverse:
        eq = Equal(S, x.set)
    else:
        eq = Equal(x.set, S)
    return Any[x](eq)


@prove
def prove(Eq):
    from axiom import sets

    S = Symbol.S(etype=dtype.integer)
    Eq << apply(Equal(abs(S), 1))

    Eq << Greater(abs(S), 0, plausible=True)

    Eq << Eq[-1].subs(Eq[0])

    Eq << sets.is_positive.imply.is_nonemptyset.apply(Eq[-1])

    Eq << sets.is_nonemptyset.imply.any_contains.apply(Eq[-1], simplify=False)

    Eq << Eq[-1].this.expr.apply(sets.contains.imply.subset, simplify=False)

    Eq << Eq[-1].this.expr.apply(sets.eq.subset.imply.eq, Eq[0])


if __name__ == '__main__':
    run()

