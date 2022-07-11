from util import *


@apply
def apply(n, P_quote=None):
    from axiom.discrete.imply.all_et.mapping.Qu2v import predefined_symbols
    Q, w, x = predefined_symbols(n)
    if P_quote is None:
        P_quote = Symbol("P'", conditionset(x[:n + 1], Equal(x[:n].cup_finiteset(), Range(n)) & Equal(x[n], n)))

    return Equal(Q[n], P_quote)


@prove
def prove(Eq):
    from axiom import sets, algebra, discrete

    n = Symbol(integer=True, positive=True)
    Eq << apply(n)

    Eq << sets.imply.all.conditionset.apply(Eq[-1].lhs)

    Eq << algebra.all_et.imply.et.all.apply(Eq[-1])

    Eq << Eq[-3].this.expr.apply(discrete.eq.eq.imply.eq.permutation.pop_back.interval)

    Eq.all_P_quote = Eq[-1] & Eq[-3]

    Eq << sets.imply.all.conditionset.apply(Eq[1].lhs)

    Eq << algebra.all_et.imply.et.all.apply(Eq[-1])

    Eq << Eq[-3].this.expr.apply(discrete.eq.eq.imply.eq.permutation.push_back)

    Eq <<= Eq[-1] & Eq[-3]

    Eq << sets.all.all.imply.eq.apply(Eq.all_P_quote, Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-07-09
