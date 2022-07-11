from util import *


@apply
def apply(n):
    x = Symbol(shape=(oo,), integer=True, nonnegative=True)
    return Equal(Card(conditionset(x[:n], Equal(x[:n].cup_finiteset(), Range(n)))), factorial(n))


@prove
def prove(Eq):
    from axiom import discrete, algebra, sets

    n = Symbol(integer=True, positive=True, given=False)
    Eq << apply(n)

    Eq.initial = Eq[-1].subs(n, 1)

    Eq << Eq.initial.this.lhs.arg.limits[0][1].simplify()

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << discrete.cup.to.condset.P2Q_union.apply(n)

    Q = Eq[-1].lhs.expr.base
    Eq << Eq[-1].apply(sets.eq.imply.eq.card)

    Eq << discrete.abs_cup.to.sum_abs.permutation.nonoverlapping.apply(n, Q=Q)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << discrete.abs_condset.inbetween.apply(n, Q=Q)

    P_quote = Eq[-1].rhs.arg
    Eq << Eq[-2].this.rhs.expr.subs(Eq[-1])

    Eq << discrete.abs_condset.last.apply(n, P_quote=P_quote)

    Eq.P_definition = Eq[-1].lhs.arg.this.definition

    Eq.recursion = Eq[-2].subs(Eq[-1].reversed)

    Eq.Pn1_definition = Eq.recursion.lhs.arg.this.definition

    Eq << Eq[0].subs(Eq.P_definition.reversed)

    Eq << Eq.recursion.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(discrete.mul.to.factorial)

    Eq << Eq.induct.subs(Eq.Pn1_definition.reversed)

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.cond.infer.imply.cond.induct.apply(Eq.initial, Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

# created on 2020-08-07
