from util import *


@apply
def apply(w):
    n = w.shape[0]
    i = w.generate_var(integer=True)
    j = w.generate_var({i}, integer=True)

    assert len(w.shape) == 4 and all(s == n for s in w.shape)
    assert w[i, j].is_SwapMatrix or w[i, j].definition.is_SwapMatrix

    return Equal(w[i, j], w[j, i])


@prove
def prove(Eq):
    from axiom import discrete, algebra
    n = Symbol(domain=Range(2, oo))
    i, j = Symbol(domain=Range(n))

    assert Identity(n).is_integer
    w = Symbol(Lamda[j, i](SwapMatrix(n, i, j)))

    Eq << apply(w)

    Eq << w[j, i].this.definition

    Eq << Eq[0] @ Eq[-1]

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.simplify(deep=True, wrt=Eq[-1].rhs.variable)

    Eq << Eq[-1].this.rhs.expr.args[-1].expr.args[0].apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.piece.to.kroneckerDelta)

    Eq << Eq[-1].this.rhs.apply(algebra.lamda.to.identity)

    Eq << discrete.matpow.to.identity.apply(w)

    Eq << Eq[-1].subs(Eq[-2].reversed)

    Eq << w[i, j].inverse() @ Eq[-1]

    Eq << Eq[-1].apply(algebra.cond.imply.all.restrict, (i,), (j,))


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-08-25
# updated on 2020-08-25
