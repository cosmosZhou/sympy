from util import *


@apply
def apply(*given, j=None):
    a_size, xa_equality = given
    a_set_comprehension_abs, n = a_size.of(Equal)
    a_set_comprehension = a_set_comprehension_abs.of(Abs)
    x_set_comprehension, _a_set_comprehension = xa_equality.of(Equal)

    assert a_set_comprehension == _a_set_comprehension

    assert len(x_set_comprehension.limits) == 1
    k, a, b = x_set_comprehension.limits[0]
    assert n == b - a

    assert len(a_set_comprehension.limits) == 1
    k, a, b = a_set_comprehension.limits[0]
    assert n == b - a

    x = Lamda(x_set_comprehension.function.arg, *x_set_comprehension.limits).simplify()
    a = Lamda(a_set_comprehension.function.arg, *a_set_comprehension.limits).simplify()

    if j is None:
        j = Symbol.j(domain=Range(0, n), given=True)

    assert j >= 0 and j < n

    index = index_function(n)
    index_j = index[j](x[:n], a[:n], evaluate=False)
    return Contains(index_j, Range(0, n)), Equal(x[index_j], a[j])


def index_function(n):
    k = Symbol.k(integer=True)

    def index(x, a, *indices):
        (j,), *_ = indices
        return Lamda[k:n](KroneckerDelta(x[k], a[j])) @ Lamda[k:n](k)

    f = Function.index(nargs=(2,), shape=(), integer=True)
    f.eval = index
    return f


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(domain=Range(2, oo), given=True)

    x = Symbol.x(shape=(n,), integer=True, given=True)

    a = Symbol.a(shape=(n,), integer=True, given=True)

    k = Symbol.k(integer=True)

    j = Symbol.j(domain=Range(0, n), given=True)

    Eq << apply(Equal(abs(a.set_comprehension(k)), n),
                Equal(x[:n].set_comprehension(k), a.set_comprehension(k)),
                j=j)

    Eq << Eq[2].lhs.this.defun()

    Eq <<= Eq[-3].subs(Eq[-1]), Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].lhs.indices[0].this.expand()

    Eq << Eq[-1].rhs.function.args[1].this.astype(Piecewise)

    Eq << Eq[-2].this.rhs.subs(Eq[-1])

    sj = Symbol.s_j(conditionset(k, Equal(a[j], x[k]), Range(0, n)))

    Eq.sj_definition = sj.this.definition

    Eq << Sum[k:sj](k).this.limits[0][1].definition

    Eq << Eq[-1].this.rhs.split({0})

    Eq.crossproduct = algebra.eq.eq.imply.eq.transit.apply(Eq[-3], Eq[-1])

    Eq.sj_definition_reversed = Eq.sj_definition.this.rhs.limits[0][1].reversed.reversed

    Eq << Eq[1].apply(sets.eq.imply.eq.intersection, {a[j]})

    k_ = Eq[-1].find(Cup).variable
    Eq << Piecewise((x[k_].set, Equal(x[k_], a[j])), (x[k_].emptySet, True)).this.simplify()

    Eq << sets.eq.imply.eq.cup.apply(Eq[-1].reversed, (k_, 0, n))

    Eq.distribute = Eq[-1].subs(Eq[-3]).reversed

    Eq << Eq.distribute.this.lhs.apply(sets.imageset.inner_subs)

    Eq << Eq[-1].subs(Eq.sj_definition_reversed)

    Eq.sj_greater_than_1 = sets.is_nonemptyset.imply.ge.apply(Eq[-1])

    Eq.distribute = Eq.distribute.subs(Eq.sj_definition_reversed)

    Eq.ou = sets.imply.ou.ne.apply(Eq.sj_greater_than_1.lhs.arg)

    Eq.sj_less_than_1 = Eq.ou.args[0].copy(plausible=True)

    Eq.inequality_ab = Eq.ou.args[1].copy(plausible=True)

    (a, *_), (b, *_) = Eq.inequality_ab.limits

    Eq << Eq[1].apply(algebra.eq.imply.eq.abs)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-1], Eq[0])

    Eq << sets.eq.imply.all_ne.complement.apply(Eq[-1], exclude=a)

    Eq << Eq[-1].subs(k_, a)

    Eq << algebra.all.imply.ou.subs.apply(Eq[-1], Eq[-1].variable, b)

    Eq << algebra.cond.any.imply.any_et.apply(Eq[-1], Eq.inequality_ab)

    Eq.distribute_ab = Eq[-1].this.function.apply(algebra.et.imply.ou)

    Eq.j_equality = sets.imply.all.conditionset.apply(sj)

    Eq << Eq.j_equality.limits_subs(k, a)

    Eq << algebra.all.any.imply.any_et.apply(Eq.j_equality.reversed, Eq.distribute_ab)

    Eq << Eq[-1].this.function.apply(algebra.et.imply.et.subs, index=1)

    Eq << Eq[-1].this.function.apply(algebra.et.imply.et.delete, index=2)

    Eq << Eq.j_equality.limits_subs(a, b)

    Eq << algebra.all.any.imply.any_et.apply(Eq.j_equality, Eq[-1])

    Eq <<= Eq.ou & ~Eq.inequality_ab

    Eq << algebra.et.imply.cond.apply(Eq[-1], index=0)

    Eq <<= Eq.sj_less_than_1 & Eq.sj_greater_than_1

    Eq << sets.eq.imply.contains.sum.apply(Eq[-1], var=k)

    Eq.index_domain = Eq[-1].subs(Eq.crossproduct.reversed)

    Eq.ou = algebra.all.imply.ou.subs.apply(Eq.j_equality, Eq.j_equality.variable, Eq.index_domain.lhs)

    Eq << Eq.ou.args[0].copy(plausible=True)

    Eq << Eq.ou.args[1].copy(plausible=True)

    Eq <<= Eq[-2] & Eq.index_domain

    Eq <<= Eq.ou & ~Eq[-2]

    Eq << algebra.et.imply.cond.apply(Eq[-1], index=1)

    Eq << Eq[-2].reversed

    Eq << Subset(sj, Eq[2].rhs, plausible=True)

    Eq << sets.contains.subset.imply.contains.apply(Eq.index_domain, Eq[-1])


if __name__ == '__main__':
    run()

# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
