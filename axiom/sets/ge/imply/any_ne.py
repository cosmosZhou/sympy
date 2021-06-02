from util import *

# given: |A| >= 1
# A != {}


@apply
def apply(given):
    assert isinstance(given, GreaterEqual)
    S_abs, positive = given.args
    assert S_abs.is_Abs and positive > 1
    S = S_abs.arg

    x = S.element_symbol()
    y = S.element_symbol({x})

    return Exists[x:S, y:S](Unequal(x, y))


@prove
def prove(Eq):
    from axiom import sets, algebra
    S = Symbol.S(etype=dtype.integer, given=True)

    Eq << apply(abs(S) >= 2)

    Eq << sets.ge.imply.any_contains.apply(Eq[0], simplify=False)

    Eq << sets.any_contains.imply.any_contains.limits_restricted.apply(Eq[-1], simplify=False)

    Eq << Eq[-1].this.function.apply(sets.contains.imply.eq.union)
    i = Eq[-1].variable

    Eq << Eq[-1].this.function.apply(algebra.eq.imply.eq.abs)

    Eq << sets.imply.eq.principle.addition.apply(S, i.set)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.function - 1

    Eq << Eq[0] - 1

    Eq << algebra.any_eq.cond.imply.any.subs.apply(Eq[-2].reversed, Eq[-1])

    Eq << Eq[-1].this.function.apply(sets.ge.imply.is_nonemptyset, simplify=False)

    i, j = Eq[1].variables
    Eq << Exists[i:S, j:S](Contains(j, Eq[-1].lhs), plausible=True)

    Eq << Eq[-1].simplify()

    Eq << ~Eq[1]

    Eq << algebra.all_eq.any.imply.any.subs.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()

