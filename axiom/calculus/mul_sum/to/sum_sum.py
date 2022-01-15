from util import *


@apply
def apply(A, B, n=None, k=None, x=None):

    if x is None:
        x = Symbol.x(real=True)

    if n is None:
        n = Symbol.n(integer=True)
    if k is None:
        k = Symbol.k(integer=True)

    return Equal(Sum[n:0:oo](A[n] * x ** n) * Sum[n:0:oo](B[n] * x ** n), Sum[n:0:oo](Sum[k:0:n + 1](A[n - k] * B[k]) * x ** n))


@prove
def prove(Eq):
    from axiom import algebra

    A, B = Symbol(shape=(oo,), real=True)
    Eq << apply(A, B)

    Eq << Eq[0].lhs.this.apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.mul.to.sum)

    i, n = Eq[-1].rhs.variables
    k = Eq[0].rhs.expr.args[1].variable
    Eq << Eq[-1].this.rhs.limits_subs(i, k)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.swap)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.subs.offset, -k)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.swap.intlimit)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.separate)


if __name__ == '__main__':
    run()
    # created on 2020-06-28
