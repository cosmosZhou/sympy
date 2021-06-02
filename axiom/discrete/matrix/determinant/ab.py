from util import *


@apply
def apply(a, b):
    n = a.shape[0]

    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)

    return Equal(Det(Lamda[j:n, i:n](a[Min(i, j)] * b[Max(i, j)])),
                    a[0] * b[n - 1] * Product(a[i] * b[i - 1] - a[i - 1] * b[i], (i, 1, n)))


@prove
def prove(Eq):
    from axiom import algebra
    n = 5
    a = Symbol.a(shape=(n,), complex=True, zero=False)
    b = Symbol.b(shape=(n,), complex=True, zero=False)
    Eq << apply(a, b)

    Eq << Symbol.L(Eq[0].lhs.arg).this.definition

    Eq << Eq[-1].this.rhs.astype(Matrix)

    Eq << Eq[-1] @ Multiplication(n, 0, 1 / a[0])

    Eq << Eq[-1] @ Multiplication(n, n - 1, 1 / b[n - 1])

    Eq << Eq[-1] @ Multiplication(n, n - 2, 1 / b[n - 2])

    Eq << Multiplication(n, n - 1, b[n - 2]) @ Eq[-1]

    Eq << Eq[-1].apply(algebra.eq.imply.eq.det)

    Eq << Eq[-1].subs(Eq[1])

    Eq << Eq[-1].reversed + Eq[0] / (a[0] * b[n - 1])

    Eq << Eq[-1].this.rhs.doit()

    Eq << Eq[-1].this.rhs.expand()


if __name__ == '__main__':
    run()
