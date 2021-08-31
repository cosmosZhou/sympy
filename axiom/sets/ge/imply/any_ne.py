from util import *


@apply
def apply(given, *vars):
    S, positive = given.of(Card >= Expr)
    assert positive > 1

    if vars:
        x, y = vars
    else:
        x = S.element_symbol()
        y = S.element_symbol({x})

    return Any[x:S, y:S](Unequal(x, y))


@prove
def prove(Eq):
    from axiom import sets, algebra

    S = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Card(S) >= 2)

    Eq << sets.ge.imply.any_el.apply(Eq[0], simplify=False)

    Eq << sets.any_el.imply.any_el.limits_restricted.apply(Eq[-1], simplify=False)

    Eq << Eq[-1].this.expr.apply(sets.el.imply.eq.union)

    i = Eq[-1].variable
    Eq << Eq[-1].this.expr.apply(sets.eq.imply.eq.card)

    Eq << sets.imply.eq.principle.add.apply(S, i.set)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.expr - 1

    Eq << Eq[0] - 1

    Eq << algebra.any_eq.cond.imply.any.subs.apply(Eq[-2].reversed, Eq[-1])

    Eq << Eq[-1].this.expr.apply(sets.ge.imply.is_nonempty, simplify=False)

    i, j = Eq[1].variables
    Eq << Any[i:S, j:S](Element(j, Eq[-1].lhs), plausible=True)

    Eq << Eq[-1].simplify()

    Eq << ~Eq[1]

    Eq << algebra.all_eq.any.imply.any.subs.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()

