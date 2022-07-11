from util import *


@apply
def apply(x, w=None, left=True, reference=True):
    n = x.shape[0]
    i, j, k = Symbol(integer=True)

    if w is None:
        w = Symbol(Lamda[j, i](SwapMatrix(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)

    if left:
        if reference:
            return Equal(Lamda[k:n](x[w[i, j, k] @ Lamda[k:n](k)]), w[i, j] @ x)
        else:
            return Equal(x[w[i, j, k] @ Lamda[k:n](k)], w[i, j, k] @ x)
    else:
        if reference:
            return Equal(Lamda[k:n](x[Lamda[k:n](k) @ w[i, j, k]]), x @ w[i, j])
        else:
            return Equal(x[Lamda[k:n](k) @ w[i, j, k]], x @ w[i, j, k])


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), real=True)
    Eq << apply(x)

    w = Eq[0].lhs.base
    i, j = Eq[0].lhs.indices
    k = Eq[1].lhs.variable
    Eq << (Eq[0].lhs[k] @ Lamda[k:n](k)).this.args[0].definition

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)

    Eq << Eq[-1].this(i).rhs.args[0].expr.simplify()

    Eq << Eq[-1].this(j).rhs.args[1].expr.simplify()

    Eq << Eq[-1].this(k).rhs.args[2].simplify()

    Eq.lhs_assertion = x[Eq[-1].lhs].this.subs(Eq[-1]).this.rhs.expand()

    Eq << (w[i, j] @ x).this.subs(Eq[0])

    Eq << Eq[-1].subs(Eq[-1].rhs.this.apply(discrete.matmul.to.lamda))

    Eq << Eq[-1].this(i).find(Element).simplify()

    Eq << Eq[-1].this(j).find(Element).simplify()

    Eq << Eq[-1].this.rhs().find(Element).simplify()

    
    Eq << Eq[-1][k]
    Eq << Eq.lhs_assertion.subs(Eq[-1].reversed)
    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (k, 0, n))
    
    


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-08-26
# updated on 2022-01-08