from util import *


@apply
def apply(n, w=None):
    domain = Range(0, n)
    t = Symbol.t(domain=domain)
    i = Symbol.i(domain=domain)
    j = Symbol.j(domain=domain)
    assert n >= 2
    if w is None:
        w = Symbol.w(Lamda[j, i](Swap(n, i, j)))

    return ForAll(Equal(w[t, i] @ w[t, j] @ w[t, i], w[i, j]), (j, domain // {i, t}))


@prove
def prove(Eq):
    from axiom import discrete, sets, algebra
    n = Symbol.n(domain=Range(2, oo))
    Eq << apply(n)

    i, _ = Eq[-1].rhs.indices
    j = Symbol.j(domain=Range(0, n))
    w = Eq[0].lhs.base

    t = Eq[1].function.lhs.args[0].indices[0]

    p = Symbol.p(complex=True)

    x = Lamda[i:n](p ** i)

    eq = Eq[0].subs(i, t)

    assert eq.lhs.args[-1] == j

    assert eq.rhs.args[-1] == j

    Eq << (w[t, i] @ x).this.subs(Eq[0].subs(i, t).subs(j, i))

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1].this.rhs().function.simplify()

    Eq << (w[t, j] @ Eq[-1]).this.rhs.subs(w[t, j].this.definition)

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1].this.rhs.function.args[1].expr.astype(Piecewise)

    Eq << Eq[-1].this.rhs.function.args[-1].expr.astype(Piecewise)

    Eq << Eq[-1].this.rhs().function.simplify(wrt=True)

    Eq << Eq[-1].this.rhs.function.args[-1].expr.astype(Add)

    Eq << Eq[-1].this.rhs().function.apply(algebra.piecewise.swap.back)

    Eq << Eq[-1].this.rhs().function.args[2].cond.simplify()

    Eq << Eq[-1].this.rhs.function.args[2].cond.apply(sets.contains.to.ou.split.finiteset)

    Eq << Eq[-1].this.rhs().function.apply(algebra.piecewise.invert, index=1)

    Eq << Eq[-1].this.rhs.function.apply(algebra.piecewise.subs, index=2)

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], (j,))

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], Eq[1].limits[0])

    Eq << Eq[-1].this().function.simplify()

    Eq << (w[t, i] @ Eq[-1]).this.function.rhs.subs(w[t, i].this.definition)

    Eq << Eq[-1].this.function.rhs.expand()

    Eq << Eq[-1].this().function.rhs().function.simplify(wrt=True)

    Eq << Eq[-1].this().function.rhs().function.args[-1].expr.args[1].apply(algebra.piecewise.swap.front)

    Eq << Eq[-1].this.function.rhs.function.astype(KroneckerDelta)

    Eq.www_expansion = Eq[-1].this().function.rhs.function.simplify()

    j = j.unbounded
    Eq << (w[i, j] @ x).this.subs(w[i, j].this.definition).this.rhs.expand()

    Eq << Eq[-1].this(j).rhs().function.simplify(wrt=True)

    Eq << Eq[-1].this.rhs.function.astype(KroneckerDelta)

    Eq << Eq[-1].this.rhs.function.expand()

    Eq << Eq.www_expansion.subs(Eq[-1].reversed)

    Eq << Eq[-1].this.function.apply(discrete.matrix.independence.rmatmul_equal)


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
