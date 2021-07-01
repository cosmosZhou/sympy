from util import *


@apply
def apply(self):
    A, B = self.of(Determinant[Expr @ Expr])

    return Equal(self, Det(A) * Det(B))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol.n(integer=True, positive=True)
    A = Symbol.A(shape=(n, n), complex=True)
    B = Symbol.B(shape=(n, n), complex=True)
    Eq << apply(Determinant(A @ B))

    Eq << (BlockMatrix([[A, ZeroMatrix(n, n)], [Identity(n), B]]) @ BlockMatrix([[Identity(n), -B], [ZeroMatrix(n, n), Identity(n)]])).this.apply(discrete.matmul.to.blockMatrix)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.blockMatrix)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.blockMatrix)

    Eq << Eq[-1].this.rhs.find(MatMul[BlockMatrix]).apply(discrete.matmul.to.blockMatrix)

    Eq << Eq[-1].this.rhs.find(MatMul[Transpose[BlockMatrix]]).apply(discrete.matmul.to.blockMatrix)

    Eq << Eq[-1].this.rhs.find(Add).apply(algebra.add.to.transpose)

    Eq << Eq[-1].this.rhs.find(Add).apply(algebra.add.to.blockMatrix)

    Eq << discrete.eq.imply.eq.det.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(discrete.det.to.det.right)

    Eq << Eq[-1].this.lhs.apply(discrete.det_blockMatrix.to.mul)

    

    Eq << Eq[-1].this.rhs.apply(discrete.det_blockMatrix.to.mul)

    Eq << Eq[-1].this.rhs.find(Det).apply(discrete.det_mul.to.mul)

    Eq << Eq[-1].this.find(Pow).apply(algebra.pow.to.one)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()