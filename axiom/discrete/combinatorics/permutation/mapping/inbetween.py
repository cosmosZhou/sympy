from util import *

from axiom.discrete.combinatorics.permutation import mapping


@apply
def apply(n, Q=None):
    if Q is None:
        Q, w, x = mapping.Qu2v.predefined_symbols(n)
    else:
        x = Q.definition.function.variable
    P_quote = Symbol("P'", conditionset(x[:n + 1], Equal(x[:n].set_comprehension(), Range(0, n)) & Equal(x[n], n)))

    t = Q.definition.variable
    return Equal(Abs(Q[t]), Abs(P_quote))


@prove
def prove(Eq):
    from axiom import discrete, sets
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)

    Eq << discrete.combinatorics.permutation.mapping.identity_Qn.apply(n)

    Eq << Eq[2].subs(Eq[-1].reversed)

    u = Eq[-1].lhs.arg.indices[0]
    Eq << mapping.Qu2v.apply(n, n, u)

    Eq << mapping.Qu2v.apply(n, u, n)

    Eq << sets.all_et.all_et.imply.eq.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
