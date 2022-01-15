from util import *


@apply
def apply(lamda):
    (A, b), (i, *i_ab) = lamda.of(Lamda[ReducedSum[Mul]])

    if b._has(i):
        A, b = b, A
    assert not b._has(i)
    A = Lamda(A, (i, *i_ab)).simplify()

    rhs = A @ b
    return Equal(lamda, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import discrete, algebra

    i, j = Symbol(integer=True)
    n, m = Symbol(integer=True, positive=True)
    A = Symbol(shape=(n, m), real=True)
    b = Symbol(real=True, shape=(m,))
    Eq << apply(Lamda[i:n](ReducedSum(A[i] * b)))

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.lhs.apply(algebra.reducedSum.to.sum)
    Eq << Eq[-1].this.lhs.simplify()


if __name__ == '__main__':
    run()
# created on 2020-11-10
