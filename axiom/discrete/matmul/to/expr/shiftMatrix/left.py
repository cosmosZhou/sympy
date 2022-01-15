from util import *


@apply
def apply(x, w=None):
    n = x.shape[0]
    i, j = Symbol(domain=Range(n))

    if w is None:
        w = Symbol.w(Lamda[j, i](ShiftMatrix(n, i, j)))
    else:
        assert w[i, j] == ShiftMatrix(n, i, j)

    return Equal(w[i, j].T @ w[i, j] @ x, x)


@prove
def prove(Eq):
    from axiom import discrete, algebra
    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), real=True)
    Eq << apply(x)

    Eq << Eq[0].T

    i, j = Eq[0].lhs.indices

    w = Eq[0].lhs.base

    Eq << (w[i, j] @ x).this.subs(Eq[0])
    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.expr.args[-1].expr.apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs().expr.args[2]().expr.simplify(wrt=Eq[-1].rhs.variable)

    Eq << Eq[-1].this.rhs().expr.args[2].expr.args[2]().expr.simplify()

    Eq << (w[i, j].T @ Eq[-1]).this.rhs.subs(Eq[0])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.expr.args[1].expr.apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs().expr.args[2]().expr.simplify(wrt=Eq[-1].rhs.variable)

    Eq << Eq[-1].this.rhs().expr.args[1]().expr.simplify()


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-11-13
