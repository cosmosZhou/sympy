from util import *


@apply
def apply(n):
    from axiom.discrete.imply.all_et.mapping.Qu2v import predefined_symbols
    Q, w, x = predefined_symbols(n)

    Pn1 = Symbol("P_{n+1}", conditionset(x[:n + 1], Equal(x[:n + 1].cup_finiteset(), Range(n + 1))))

    t = Q.definition.variable
    return Equal(Cup[t](Q[t]), Pn1)


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol(integer=True, positive=True)
    Eq << apply(n)

    Q = Eq[0].lhs.base
    t = Q.definition.variable
    Eq << Subset(Eq[0].lhs, Eq[2].rhs, plausible=True)

    Eq.subset_P = sets.subset.imply.subset.cup.lhs.apply(Eq[-1], (t,), simplify=False)

    Eq.subset_Q = Subset(Eq.subset_P.rhs, Eq.subset_P.lhs, plausible=True)

    Eq << sets.subset.given.all_el.apply(Eq.subset_Q)

    Eq << Eq[-1].limits_subs(Eq[-1].variable, Eq[0].rhs.variable)

    Eq << Eq[-1].this.expr.apply(sets.el_cup.given.any_el)

    Eq << Eq[-1].this.expr.expr.rhs.definition

    Eq << algebra.all_et.given.et.all.apply(Eq[-1])

    Eq << Eq[-1].this.limits[0][1].definition

    Eq << Eq[-2].this.limits[0][1].definition

    Eq << algebra.all.given.infer.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(sets.eq.imply.el.st.cup, index=n)

    Eq <<= Eq.subset_P & Eq.subset_Q


if __name__ == '__main__':
    run()
# created on 2020-08-04
