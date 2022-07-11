from util import *


@apply
def apply(eq_w):
    ((i, j), (S[j], S[0], n), (S[i], S[0], S[n])), w = eq_w.of(Equal[Lamda[SwapMatrix]])
    domain = Range(n)
    t, i, j = Symbol(domain=domain)
    assert n >= 2
    return All(Equal(w[t, i] @ w[t, j] @ w[t, i], w[i, j]), (j, domain - {i, t}))


@prove
def prove(Eq):
    from axiom import discrete, algebra, sets

    n = Symbol(domain=Range(2, oo))
    w = Symbol(integer=True, shape=(n, n, n, n))
    i, j = Symbol(integer=True)
    Eq << apply(Equal(w, Lamda[j:n, i:n](SwapMatrix(n, i, j))))

    i, _ = Eq[-1].rhs.indices
    j = Symbol(domain=Range(n))
    w = Eq[0].lhs
    t = Eq[1].expr.lhs.args[0].indices[0]
    p = Symbol(complex=True)
    x = Lamda[i:n](p ** i)
    eq = Eq[0][t, j]
    assert eq.lhs.args[-1] == j
    assert eq.rhs.args[-1] == j
    Eq << (w[t, i] @ x).this.subs(Eq[0].subs(i, t).subs(j, i))

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs().expr.simplify()

    Eq << (w[t, j] @ Eq[-1]).this.rhs.subs(Eq[0][t, j])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.expr.args[-1].expr.apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs.expr.args[1].expr.apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs().expr.simplify(wrt=True)

    Eq << Eq[-1].this.rhs.expr.args[-1].expr.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs().expr.apply(algebra.piece.swap, -2)

    Eq << Eq[-1].this.rhs().expr.args[2].cond.simplify()

    Eq << Eq[-1].this.rhs.expr.args[2].cond.apply(sets.el.to.ou.split.finiteset)

    Eq << Eq[-1].this.rhs().expr.apply(algebra.piece.invert, 1)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.piece.subs, index=2)

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], (j,))

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], Eq[1].limits[0])

    Eq << Eq[-1].this().expr.simplify()

    Eq << Eq[-1].this.expr.apply(discrete.eq.imply.eq.rmatmul, w[t, i])

    Eq << Eq[-1].this.expr.rhs.subs(Eq[0][t, i])

    Eq << Eq[-1].this.expr.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this().expr.rhs().expr.simplify(wrt=True)

    Eq << Eq[-1].this().expr.rhs().expr.args[-1].expr.args[1].apply(algebra.piece.swap)

    Eq << Eq[-1].this.expr.rhs.expr.apply(algebra.piece.to.kroneckerDelta)

    Eq.www_expansion = Eq[-1].this().expr.rhs.expr.simplify()

    j = j.unbounded
    Eq << (w[i, j] @ x).this.subs(Eq[0][i, j]).this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this(j).rhs().expr.simplify(wrt=True)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.piece.to.kroneckerDelta)

    Eq << Eq.www_expansion.subs(Eq[-1].reversed)

    Eq << Eq[-1].this.expr.apply(discrete.eq.imply.eq.matrix.independence.rmatmul_equal)

    
    


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-08-23
# updated on 2022-04-01
