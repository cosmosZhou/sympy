from util import *


@apply
def apply(x, y, W):
    return Equal(x @ W @ y, y @ W.T @ x)


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol.n(integer=True)
    x = Symbol.x(shape=(n,), real=True)
    y = Symbol.y(shape=(n,), real=True)
    W = Symbol.W(shape=(n, n), real=True)
    Eq << apply(x, y, W)

    i = Symbol.i(domain=Range(0, n))
    j = Symbol.j(domain=Range(0, n))
    Eq << (x @ W).this.apply(discrete.matmul.to.lamda, var={i, j})

    Eq << Eq[-1] @ y

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)

    Eq.expansion = Eq[-1].this.rhs.expr.apply(algebra.mul.to.sum)

    Eq << Eq.expansion.subs(W, W.T)

    Eq << Eq[-1].apply(algebra.eq.imply.eq.swap, x, y)

    Eq << Eq[-1].this.rhs.limits_subs(i, j)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.swap)

    Eq << Eq.expansion.subs(Eq[-1].reversed)


if __name__ == '__main__':
    run()
