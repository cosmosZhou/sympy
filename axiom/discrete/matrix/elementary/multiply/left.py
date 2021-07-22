from util import *


@apply
def apply(x, lamda, w=None):
    n = x.shape[0]
    i = Symbol.i(domain=Range(0, n))

    if w is None:
        w = Symbol.w(Lamda[i](Multiplication(n, i, lamda)))
        w_quote = Symbol.w_quote(Lamda[i](Multiplication(n, i, 1 / lamda)))
    else:
        assert w[i] == Multiplication(n, i, lamda)
        assert w_quote[i] == Multiplication(n, i, 1 / lamda)

    return Equal(w_quote[i] @ w[i] @ x, x)


@prove
def prove(Eq):
    from axiom import discrete
    n = Symbol.n(domain=Range(2, oo))
    x = Symbol.x(shape=(n,), real=True)
    lamda = Symbol.lamda(real=True)
    Eq << apply(x, lamda)

    i, *_ = Eq[0].lhs.indices

    w_quote = Eq[0].lhs.base
    w = Eq[1].lhs.base

    Eq << (w[i] @ x).this.subs(Eq[1])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << (w_quote[i] @ Eq[-1]).this.rhs.subs(Eq[0])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.args[1].expr.expand()


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
