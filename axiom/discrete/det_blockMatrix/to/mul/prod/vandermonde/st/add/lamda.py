from util import *


@apply
def apply(self):
    ((r, j1), (j, _0, n)), ((_j1, i1), j_limit, (i, __0, n_1)) = self.of(Det[BlockMatrix[1 - Lamda[Pow], Lamda[Pow]]])
    assert j_limit == (j, _0, n)
    assert 0 == _0 == __0
    assert n_1 == n - 1
    assert j1 == _j1 == j + 1
    assert i1 == i + 1

    return Equal(self, (1 - r) ** n * Product[i:n](factorial(i)))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    r = Symbol(real=True)
    n = Symbol(integer=True, positive=True)
    n = Symbol(domain=Range(2, oo))
    i, j = Symbol(integer=True)
    Eq << apply(Det(BlockMatrix([1 - Lamda[j:n](r ** (j + 1)), Lamda[j:n, i:n - 1]((j + 1) ** (i + 1))])))

    Eq << discrete.det_blockMatrix.to.mul.prod.vandermonde.st.lamda.pow.apply(Det(BlockMatrix([Lamda[j:n + 1](r ** j), Lamda[j:n + 1, i:n](j ** i)])))

    Eq << Eq[-1].lhs.arg.this.args[1].apply(discrete.lamda.to.blockMatrix.split, 1)

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], SwapMatrix(n + 1, 0, 1))

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.oneMatrix.to.blockMatrix, 1)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.lamda.to.blockMatrix.split, 1)

    Eq << Eq[-1].this.rhs.args[2].apply(algebra.lamda.to.transpose.blockMatrix, 1)

    Eq << Eq[-1].this.find(Lamda[Zero ** Add])().expr.simplify()

    Eq << Eq[-1] @ MulMatrix(n + 1, 0, -1)

    Eq << Eq[-1] @ (Identity(n + 1) + Lamda[i:n + 1](1 - KroneckerDelta(i, 0)))

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[1].subs(n, 4)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.matrix)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.matrix)

    A = Symbol(Eq[-1].lhs.arg)
    Eq << A.this.definition

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], SwapMatrix(5, 0, 1))

    Eq << Eq[-1] @ MulMatrix(5, 0, -1)

    Eq << Eq[-1] @ AddMatrix(5, 1, 0)

    Eq << Eq[-1] @ AddMatrix(5, 2, 0)

    Eq << Eq[-1] @ AddMatrix(5, 3, 0)

    Eq << Eq[-1] @ AddMatrix(5, 4, 0)

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], MulMatrix(5, 1, -1))

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], AddMatrix(5, 0, 1))

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], MulMatrix(5, 0, -1))

    
    


if __name__ == '__main__':
    run()
# created on 2020-10-14
# updated on 2021-10-16