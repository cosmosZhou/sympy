from util import *



@apply
def apply(given, x):
    assert given.is_Equal
    p_set_comprehension, interval = given.args
    assert len(p_set_comprehension.limits) == 1
    i, zero, n_1 = p_set_comprehension.limits[0]
    assert zero.is_zero
    n = n_1
    assert p_set_comprehension.expr.is_FiniteSet
    p = p_set_comprehension.expr.arg.base
    assert p_set_comprehension == p[:n].set_comprehension()
    zero, _n = interval.args
    assert zero.is_zero
    assert _n == n and interval.right_open
    return Equal(Cup[i:n](x[p[i]].set), x[:n].set_comprehension())


@prove
def prove(Eq):
    from axiom import sets, algebra, discrete

    n = Symbol.n(integer=True, positive=True)
    p = Symbol.p(integer=True, shape=(n,))
    x = Symbol.x(integer=True, shape=(n,))
    Eq << apply(Equal(p.set_comprehension(), Range(0, n)), x)

    A = Symbol.A(Eq[1].lhs)
    B = Symbol.B(Eq[1].rhs)
    Eq.A_definition = A.this.definition

    i = Eq[1].lhs.variable
    _i = Symbol.i(domain=Range(0, n))
    Eq.A_definition = Eq.A_definition.this.rhs.limits_subs(i, _i)

    j = Eq[1].rhs.variable
    _j = Symbol.j(domain=Range(0, n))
    Eq.B_definition = B.this.definition

    Eq.B_definition = Eq.B_definition.this.rhs.limits_subs(Eq.B_definition.rhs.variable, _j)

    Eq.subset = Subset(Eq.A_definition.rhs, Eq.B_definition.rhs, plausible=True)

    Eq << sets.subset.given.all_subset.split.cup.apply(Eq.subset)

    Eq << Eq[-1].apply(sets.contains.given.any_contains.st.cup)

    Eq << algebra.any.given.any.subs.apply(Eq[-1], Eq[-1].variable, p[_i])

    Eq.supset = Supset(Eq.subset.lhs, Eq.subset.rhs, plausible=True)

    Eq << sets.supset.given.all_supset.split.cup.apply(Eq.supset)

    Eq.definition = Eq[-1].apply(sets.contains.given.any_contains.st.cup)

    Eq << discrete.eq.imply.et.index.apply(Eq[0], _j)

    index_j = Eq[-1].lhs.indices[0]
    Eq << Eq.definition.subs(Eq[-1].reversed)

    Eq << algebra.any.given.any.subs.apply(Eq[-1], Eq[-1].variable, index_j)
    Eq << algebra.any.given.cond.apply(Eq[-1])

    Eq <<= Eq.subset & Eq.supset

    Eq << Eq[-1].this.lhs.limits_subs(_i, i)

    Eq << Eq[-1].this.rhs.limits_subs(_j, j)

    Eq << Eq[-1].this.lhs.apply(sets.cup.limits.domain_defined.insert)

    Eq << Eq[-1].this.rhs.apply(sets.cup.limits.domain_defined.insert)


if __name__ == '__main__':
    run()

