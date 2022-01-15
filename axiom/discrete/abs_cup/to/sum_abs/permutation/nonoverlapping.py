from util import *


@apply
def apply(n, Q=None):
    if Q is None:
        from axiom.discrete.imply.all_et.mapping.Qu2v import predefined_symbols
        Q, w, x = predefined_symbols(n)

    t = Q.definition.variable
    return Equal(Card(Cup[t](Q[t])), Sum[t](Card(Q[t])))


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol(integer=True, positive=True, given=True)
    Eq << apply(n)

    Q = Eq[0].lhs.base
    t = Q.definition.variable
    j = Symbol(integer=True)
    Eq.nonoverlapping = All[j: Range(n + 1) - {t}, t](Equal(Q[t] & Q[j], Q[t].etype.emptySet), plausible=True)

    Eq << ~Eq.nonoverlapping

    Eq << Eq[-1].this.expr.apply(sets.intersect_ne_empty.imply.any_el, wrt=Eq[0].rhs.variable, simplify=None)

    Eq << Eq[-1].this.find(Element).rhs.definition

    Eq << algebra.any_et.imply.any.split.apply(Eq[-1], index=0)

    Eq << sets.imply.all.conditionset.apply(Q[t])

    Eq << algebra.all_et.imply.all.apply(Eq[-1], index=0)

    Eq << algebra.all.any.imply.any_et.apply(Eq[-1], Eq[-3])

    Eq << sets.all_is_empty.imply.eq.nonoverlapping.setlimit.apply(Eq.nonoverlapping)


if __name__ == '__main__':
    run()
# created on 2020-08-06
