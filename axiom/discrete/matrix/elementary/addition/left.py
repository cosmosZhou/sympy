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

    return Equal(w_quote[i, j] @ w[i, j] @ x, x)


@prove
def prove(Eq):
    from axiom import discrete
    n = Symbol.n(domain=Range(2, oo))
    x = Symbol.x(shape=(n,), real=True)
    lamda = Symbol.lamda(real=True)
    Eq << apply(x, lamda)

    i, j = Eq[0].lhs.indices

    w_quote = Eq[0].lhs.base
    w = Eq[1].lhs.base

    Eq << (w[i, j] @ x).this.subs(Eq[1])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.function.args[1]().expr.simplify()

    Eq << (w_quote[i, j] @ Eq[-1]).this.rhs.subs(Eq[0])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.function.simplify(wrt=j)


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
