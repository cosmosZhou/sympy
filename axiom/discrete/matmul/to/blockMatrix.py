from util import *


def matmul(A, B, deep=False):
    if A.is_BlockMatrix:
        args_A = A.args
        if B.is_BlockMatrix and deep:
            return BlockMatrix(*[matmul(arg, B, deep=True) for arg in args_A])
        else:
            return BlockMatrix(*[MatMul(arg, B).simplify() for arg in args_A])

    elif A.is_Transpose:
        args_B = B.of(BlockMatrix)
        args_A = A.arg.of(BlockMatrix)
        assert len(args_A) == len(args_B)

        if deep:
            args = [matmul(b.T, a) for a, b in zip(args_A, args_B)]
            s = args[0]
            for i in range(1, len(args)):
                s += args[i]
            return s.T
        else:
            args = [a.T @ b for a, b in zip(args_A, args_B)]
        return Add(*args)
    else:
        args_B = B.of(Transpose[BlockMatrix])
        return BlockMatrix(*[MatMul(arg, A.T).simplify() for arg in args_B]).T

@apply
def apply(self, deep=False):
    A, B = self.of(MatMul)
    rhs = matmul(A, B, deep=deep)
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import discrete, algebra

    a, b, n, m = Symbol(integer=True, positive=True)
    C = Symbol(shape=(m, n), complex=True)
    A = Symbol(shape=(a, m), complex=True)
    B = Symbol(shape=(b, m), complex=True)
    Eq << apply(BlockMatrix(A, B) @ C)

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.to.lamda)

    i = Symbol(domain=Range(a + b))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], i)

    j = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], j)


if __name__ == '__main__':
    run()
# created on 2020-08-18
# updated on 2020-08-18
