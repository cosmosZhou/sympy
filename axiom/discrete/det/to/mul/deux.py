from util import *


@apply
def apply(self):
    A, B = self.of(Determinant[Expr @ Expr])

    return Equal(self, Det(A) * Det(B))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(integer=True, positive=True)
    A, B = Symbol(shape=(n, n), complex=True)
    Eq << apply(Determinant(A @ B))

    Eq << (BlockMatrix([[A, ZeroMatrix(n, n)], [Identity(n), B]]) @ BlockMatrix([[Identity(n), -B], [ZeroMatrix(n, n), Identity(n)]])).this.apply(discrete.matmul.to.block, deep=True)

    Eq << discrete.eq.imply.eq.det.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(discrete.det.matmul.simplify.col_transformation)

    Eq << Eq[-1].this.lhs.apply(discrete.det_block.to.mul.deux)

    Eq << Eq[-1].this.rhs.apply(discrete.det_block.to.mul.deux)

    Eq << Eq[-1].this.rhs.find(Det).apply(discrete.det_mul.to.mul)

    Eq << Eq[-1].this.find(Pow).apply(algebra.pow.to.one)

    Eq << Eq[-1].reversed





if __name__ == '__main__':
    run()
# created on 2020-08-20
# updated on 2021-12-13