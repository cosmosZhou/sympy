from util import *


@apply
def apply(n, Q=None):
    from axiom.discrete.combinatorics.permutation import mapping
    if Q is None:
        Q, w, x = mapping.Qu2v.predefined_symbols(n)

    t = Q.definition.variable
    return Equal(Abs(Cup[t](Q[t])), Sum[t](Abs(Q[t])))


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True, positive=True, given=True)
    Eq << apply(n)

    Q = Eq[0].lhs.base
    t = Q.definition.variable
    j = Symbol.j(integer=True)

    Eq.nonoverlapping = ForAll[j: Range(0, n + 1) // {t}, t](Equal(Q[t] & Q[j], Q[t].etype.emptySet), plausible=True)

    Eq << ~Eq.nonoverlapping

    Eq << Eq[-1].this.function.apply(sets.is_nonemptyset.imply.any_contains.st.intersection, wrt=Eq[0].rhs.variable, domain=Q[t], simplify=None)

    Eq << Eq[-1].this.find(Contains).rhs.definition

    Eq << algebra.any_et.imply.any.split.apply(Eq[-1], index=0)

    Eq << sets.imply.all.conditionset.apply(Q[t])

    Eq << algebra.all_et.imply.all.apply(Eq[-1], index=0)

    Eq << algebra.all.any.imply.any_et.apply(Eq[-1], Eq[-3])

    Eq << sets.all_is_emptyset.imply.eq.nonoverlapping.setlimit.apply(Eq.nonoverlapping)


if __name__ == '__main__':
    run()
