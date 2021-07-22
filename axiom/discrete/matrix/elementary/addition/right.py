from util import *


@apply
def apply(x, lamda, w=None):
    n = x.shape[0]
    i = Symbol.i(domain=Range(0, n))
    j = Symbol.j(domain=Range(0, n))

    if w is None:
        w = Symbol.w(Lamda[j, i](Addition(n, i, j, lamda)))
        w_quote = Symbol.w_quote(Lamda[j, i](Addition(n, i, j, -lamda)))
    else:
        assert w[i, j] == Addition(n, i, j, lamda)
        assert w_quote[i, j] == Addition(n, i, j, -lamda)

    return Equal(x @ w[i, j] @ w_quote[i, j], x)


@prove
def prove(Eq):
    from axiom import discrete, algebra
    n = Symbol.n(domain=Range(2, oo))
    x = Symbol.x(shape=(n,), real=True)
    lamda = Symbol.lamda(real=True)
    Eq << apply(x, lamda)

    i, j = Eq[0].lhs.indices

    w = Eq[0].lhs.base
    w_quote = Eq[1].lhs.base

    Eq << (x @ w[i, j]).this.subs(Eq[0])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs().expr.args[1].args[0].args[-1].args[1].args[0].cond.simplify()

    Eq << Eq[-1].this.rhs().expr.args[-1].args[0].cond.simplify()

    Eq << Eq[-1].this.rhs.args[1].expr.apply(algebra.piecewise.to.kroneckerDelta)

    Eq << Eq[-1].this.rhs.args[1].expr.expand()

    Eq << Eq[-1].this.rhs.args[1].expr.simplify()

    Eq << (Eq[-1] @ w_quote[i, j]).this.rhs.subs(Eq[1])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs().expr.args[1].args[0].args[-1].args[1].args[0].cond.simplify()

    Eq << Eq[-1].this.rhs().expr.args[-1].args[0].cond.simplify()

    Eq << Eq[-1].this.rhs.args[1].expr.apply(algebra.piecewise.to.kroneckerDelta)

    Eq << Eq[-1].this.rhs.args[1].expr.expand()

    Eq << Eq[-1].this.rhs.args[1].expr.simplify()


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
