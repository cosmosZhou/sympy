from util import *


@apply
def apply(n, Q=None):
    if Q is None:
        from axiom.discrete.imply.all_et.mapping.Qu2v import predefined_symbols
        Q, w, x = predefined_symbols(n)
    else:
        x = Q.definition.expr.variable
    P_quote = Symbol("P'", conditionset(x[:n + 1], Equal(x[:n].cup_finiteset(), Range(n)) & Equal(x[n], n)))

    t = Q.definition.variable
    return Equal(Card(Q[t]), Card(P_quote))


@prove
def prove(Eq):
    from axiom import discrete, sets
    n = Symbol(integer=True, positive=True)
    Eq << apply(n)

    Eq << discrete.condset.identity_Qn.apply(n)

    Eq << Eq[2].subs(Eq[-1].reversed)

    u = Eq[-1].lhs.arg.indices[0]
    Eq << discrete.imply.all_et.mapping.Qu2v.apply(n, n, u)

    Eq << discrete.imply.all_et.mapping.Qu2v.apply(n, u, n)

    Eq << sets.all_et.all_et.imply.eq.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2020-08-01
