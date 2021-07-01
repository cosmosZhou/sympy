from util import *


@apply
def apply(self):
    A, B = self.of(Determinant[Expr @ BlockMatrix[Transpose[BlockMatrix[Identity, Expr]], Transpose[BlockMatrix[ZeroMatrix, Identity]]]])
    
    return Equal(self, Det(A))


@prove(proved=False)
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    A = Symbol.A(shape=(2 * n, 2 * n), complex=True)
    B = Symbol.B(shape=(n, n), complex=True)
    Eq << apply(Determinant(A @ BlockMatrix([[Identity(n), B], [ZeroMatrix(n, n), Identity(n)]])))


if __name__ == '__main__':
    run()