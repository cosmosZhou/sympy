from util import *


@apply
def apply(self):
    (A, B), (C, D) = self.of(Determinant[BlockMatrix[BlockMatrix[1], BlockMatrix[1]]])
    if A.is_ZeroMatrix or D.is_ZeroMatrix:
        A = B
        D = C
        factor = (-1) ** (B.shape[0] * C.shape[0])
    else:
        assert B.is_ZeroMatrix or C.is_ZeroMatrix
        factor = 1

    if A.is_Transpose:
        A = A.T

    if D.is_Transpose:
        D = D.T

    return Equal(self, factor * Det(A).doit() * Det(D).doit())


@prove(proved=False)
def prove(Eq):
    from axiom import discrete

    n, m = Symbol(integer=True, positive=True)
    #A = Symbol(shape=(m, m), complex=True)
    #B = Symbol(shape=(n, n), complex=True)
    #C = Symbol(shape=(m, n), complex=True)
    #Eq << apply(Determinant(BlockMatrix([[A, C],[ZeroMatrix(n, m), B]])))
    A = Symbol(shape=(m, m), complex=True)
    B = Symbol(shape=(n, n), complex=True)
    C = Symbol(shape=(m, n), complex=True)
    Eq << apply(Determinant(BlockMatrix([[C, A],[B, ZeroMatrix(n, m)]])))

    Eq << (Eq[0].lhs.arg @ BlockMatrix([[ZeroMatrix(n, m), Identity(n)],[Identity(m), ZeroMatrix(m, n)]])).this.apply(discrete.matmul.to.block)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.block)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.block)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.block)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.block)

    Eq << discrete.eq.imply.eq.det.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(discrete.det_matmul.to.mul.right)

    #Eq << Eq[-1].this.rhs.apply(discrete.det_blockMatrix.to.mul)
    Eq << Eq[-1] * (-1) ** (m*n)





if __name__ == '__main__':
    run()

# created on 2020-08-19
# updated on 2021-12-13