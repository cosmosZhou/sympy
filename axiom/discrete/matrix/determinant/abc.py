from util import *


@apply
def apply(A):
    n = A.shape[0]
    k = Symbol.k(integer=True)
    return Equal(det(Sum[k:1:n]((Shift(n, 0, n - 1) ** k) @ A)), det(A) * (n - 1) * (-1) ** (n - 1))


@prove
def prove(Eq):
    from axiom import discrete, algebra, sets

    n = 6
    A = Symbol.A(shape=(n, n), complex=True)
    Eq << apply(A)

    Eq << Symbol.L(Eq[0].lhs.arg).this.definition

    shift = Eq[-1].rhs.expr.args[0].base
    Eq.L_definition = Eq[-1].this.rhs.doit()

    Eq << (shift @ A).this.apply(discrete.matmul.to.lamda)

    #Eq << Eq[-1].this.rhs.expr.apply(algebra.piecewise.flatten, index=1)
    #Eq << Eq[-1].this.rhs.expr.args[1].cond.args[0].apply(sets.contains.imply.contains.interval.substract, 1)
    Eq << Eq[-1].this.rhs.doit()

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], shift)

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], shift)

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], shift)

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], shift)

    Eq << Eq[-1] + Eq[-2] + Eq[-3] + Eq[-4] + Eq[-5]

    Eq << Eq.L_definition.subs(Eq[-1])

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], Addition(n, 0, 1))

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], Addition(n, 0, 2))

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], Addition(n, 0, 3))

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], Addition(n, 0, 4))

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], Addition(n, 0, 5))

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], Multiplication(n, 0, S.One / (n - 1)))

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], Addition(n, 1, 0, -1))

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], Multiplication(n, 1, -1))

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], Addition(n, 2, 0, -1))

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], Multiplication(n, 2, -1))

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], Addition(n, 3, 0, -1))

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], Multiplication(n, 3, -1))

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], Addition(n, 4, 0, -1))
    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], Multiplication(n, 4, -1))

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], Addition(n, 5, 0, -1))
    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], Multiplication(n, 5, -1))

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], Addition(n, 0, 1, -1))

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], Addition(n, 0, 2, -1))

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], Addition(n, 0, 3, -1))

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], Addition(n, 0, 4, -1))

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], Addition(n, 0, 5, -1))

    Eq << Eq[-1].apply(discrete.eq.imply.eq.det)

    Eq << Eq[-1].this.lhs.apply(discrete.det.to.mul)

    Eq << Eq[-1] * (n - 1)

    Eq << -Eq[-1].subs(Eq[1])


if __name__ == '__main__':
    run()
