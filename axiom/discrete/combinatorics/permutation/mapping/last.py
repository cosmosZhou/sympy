from util import *


@apply
def apply(n, P_quote=None):

    if P_quote is None:
        x = Symbol.x(shape=(oo,), integer=True, nonnegative=True)
        P_quote = Symbol("P'", conditionset(x[:n + 1], Equal(x[:n].set_comprehension(), Range(0, n)) & Equal(x[n], n)))
    else:
        x = P_quote.definition.variable.base

    P = Symbol.P(conditionset(x[:n], Equal(x[:n].set_comprehension(), Range(0, n))))
    return Equal(Abs(P), Abs(P_quote))


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)

    x = Eq[0].rhs.variable.base
    P = Eq[0].lhs
    P_quote = Eq[1].lhs
    i = Symbol.i(integer=True)
    x_quote = Symbol("x'", Lamda[i:n + 1](Piecewise((n, Equal(i, n)), (x[i], True))))
    Eq.x_quote_definition = x_quote.this.definition

    Eq << Eq.x_quote_definition[:n]

    Eq.mapping = Eq[-1].this.rhs().function.simplify()

    Eq << Eq.x_quote_definition[i]

    Eq << sets.eq.imply.eq.set_comprehension.apply(Eq[-1], (i, 0, n))

    Eq.x_quote_n_definition = Eq[-2].subs(i, n)

    Eq << sets.imply.all.conditionset.apply(P)

    Eq << algebra.all_eq.cond.imply.all.subs.apply(Eq[-1], Eq[-2])

    Eq.P2P_quote = All[x[:n]:P](Contains(x_quote, P_quote), plausible=True)

    Eq << Eq.P2P_quote.this.function.rhs.definition

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq << sets.imply.all.conditionset.apply(P_quote)

    Eq << algebra.all_et.imply.et.all.apply(Eq[-1])

    Eq << algebra.cond.all.imply.all_et.apply(Eq.x_quote_n_definition, Eq[-2], simplify=False)

    Eq << Eq[-1].this.function.apply(algebra.eq.eq.imply.eq.transit)

    Eq.mapping_quote = All[x[:n + 1]:P_quote](Equal(x_quote, x[:n + 1]), plausible=True)

    Eq << Eq.mapping_quote.this.function.apply(algebra.eq.given.et.split.blockmatrix, slice(-1))

    Eq << algebra.all_et.given.all.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.mapping)

    Eq << All[x[:n + 1]:P_quote](Contains(x[:n], P), plausible=True)

    Eq << Eq[-1].this.function.rhs.definition

    Eq << sets.all_contains.all_contains.all_eq.all_eq.imply.eq.apply(Eq[-1], Eq.P2P_quote, Eq.mapping_quote, Eq.mapping)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
