from util import *


@apply
def apply(a_size, xa_equality, j=None):
    a_cup_finiteset, n = a_size.of(Equal[Card])
    x_cup_finiteset, _a_cup_finiteset = xa_equality.of(Equal)

    assert a_cup_finiteset == _a_cup_finiteset

    xexpr, (k, a, b) = x_cup_finiteset.of(Cup[FiniteSet])
    assert n == b - a

    aexpr, (_k, _a, _b) = a_cup_finiteset.of(Cup[FiniteSet])
    assert n == _b - _a

    x = Lamda[k:a:b](xexpr).simplify()
    a = Lamda[_k:_a:_b](aexpr).simplify()

    if j is None:
        j = Symbol(domain=Range(n), given=True)

    assert j >= 0 and j < n

    from axiom.discrete.eq.imply.et.index import index_function
    index = index_function(n)
    index_j = index[j](x[:n], a[:n], evaluate=False)
    return Element(index_j, Range(n)), Equal(x[index_j], a[j])


@prove
def prove(Eq):
    from axiom import discrete, algebra, sets

    n = Symbol(domain=Range(2, oo), given=True)
    x, a = Symbol(shape=(n,), integer=True, given=True)
    k = Symbol(integer=True)
    j = Symbol(domain=Range(n), given=True)
    Eq << apply(Equal(Card(a.cup_finiteset(k)), n),
                Equal(x[:n].cup_finiteset(k), a.cup_finiteset(k)),
                j=j)

    Eq << Eq[2].lhs.this.defun()

    Eq <<= Eq[-3].subs(Eq[-1]), Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].lhs.indices[0].this.apply(discrete.matmul.to.sum)

    Eq << Eq[-1].rhs.expr.args[1].this.apply(algebra.kroneckerDelta.to.piece)

    Eq << algebra.eq.eq.imply.eq.subs.rhs.apply(Eq[-1], Eq[-2])

    s_j = Symbol(conditionset(k, Equal(a[j], x[k]), Range(n)))
    Eq.s_j_definition = s_j.this.definition

    Eq << Sum[k:s_j](k).this.limits[0][1].definition

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add.split, cond={0})

    Eq.crossproduct = algebra.eq.eq.imply.eq.transit.apply(Eq[-3], Eq[-1])

    Eq.s_j_definition_reversed = Eq.s_j_definition.this.rhs.limits[0][1].reversed.reversed

    Eq << Eq[1].apply(sets.eq.imply.eq.intersect, {a[j]})

    k_ = Eq[-1].find(Cup).variable
    Eq << Piecewise((x[k_].set, Equal(x[k_], a[j])), (x[k_].emptySet, True)).this.simplify()

    Eq << sets.eq.imply.eq.cup.apply(Eq[-1].reversed, (k_, 0, n))

    Eq.distribute = Eq[-1].subs(Eq[-3]).reversed

    Eq << Eq.distribute.this.lhs.apply(sets.imageset.inner_subs)

    Eq << Eq[-1].subs(Eq.s_j_definition_reversed)

    Eq.s_j_greater_than_1 = sets.ne_empty.imply.ge.apply(Eq[-1])

    Eq.distribute = Eq.distribute.subs(Eq.s_j_definition_reversed)

    Eq.ou = sets.imply.ou.ne.apply(Eq.s_j_greater_than_1.lhs.arg)

    Eq.s_j_less_than_1 = Eq.ou.args[0].copy(plausible=True)

    Eq.inequality_ab = Eq.ou.args[1].copy(plausible=True)

    (a, *_), (b, *_) = Eq.inequality_ab.limits
    Eq << Eq[1].apply(sets.eq.imply.eq.card)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-1], Eq[0])

    Eq << sets.eq.imply.all_ne.complement.apply(Eq[-1], exclude=a)

    Eq << Eq[-1].subs(k_, a)

    Eq << algebra.all.imply.ou.subs.apply(Eq[-1], Eq[-1].variable, b)

    Eq << algebra.cond.any.imply.any_et.apply(Eq[-1], Eq.inequality_ab)

    Eq.distribute_ab = Eq[-1].this.expr.apply(algebra.et.imply.ou)

    Eq.j_equality = sets.imply.all.conditionset.apply(s_j)

    Eq << Eq.j_equality.limits_subs(k, a)

    Eq << algebra.all.any.imply.any_et.apply(Eq.j_equality.reversed, Eq.distribute_ab)

    Eq << Eq[-1].this.expr.apply(algebra.et.imply.et.subs, index=1)

    Eq << Eq[-1].this.expr.apply(algebra.et.imply.et.delete, index=2)

    Eq << Eq.j_equality.limits_subs(a, b)

    Eq << algebra.all.any.imply.any_et.apply(Eq.j_equality, Eq[-1])

    Eq <<= Eq.ou & ~Eq.inequality_ab

    Eq << algebra.et.imply.cond.apply(Eq[-1], index=0)

    Eq <<= Eq.s_j_less_than_1 & Eq.s_j_greater_than_1

    Eq << sets.eq.imply.el.sum.apply(Eq[-1], var=k)

    Eq.index_domain = Eq[-1].subs(Eq.crossproduct.reversed)

    Eq.ou = algebra.all.imply.ou.subs.apply(Eq.j_equality, Eq.j_equality.variable, Eq.index_domain.lhs)

    Eq << Eq.ou.args[0].copy(plausible=True)

    Eq << Eq.ou.args[1].copy(plausible=True)

    Eq <<= Eq[-2] & Eq.index_domain

    Eq <<= Eq.ou & ~Eq[-2]

    Eq << algebra.et.imply.cond.apply(Eq[-1], index=1)

    Eq << Eq[-2].reversed

    Eq << Subset(s_j, Eq[2].rhs, plausible=True)

    Eq << sets.el.subset.imply.el.apply(Eq.index_domain, Eq[-1])


if __name__ == '__main__':
    run()

# https://docs.sympy.org/latest/modules/combinatorics/permutations.html

# created on 2020-07-22
