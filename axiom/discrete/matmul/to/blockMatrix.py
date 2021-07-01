from util import *


@apply
def apply(self):
    A, B = self.of(MatMul)
    if A.is_BlockMatrix:
        args_A = A.args
        rhs = BlockMatrix(*[MatMul(arg, B).simplify() for arg in args_A])    
    elif A.is_Transpose:
        args_B = B.of(BlockMatrix)
        args_A = A.arg.of(BlockMatrix)
        assert len(args_A) == len(args_B)
        
        args = [a.T @ b for a, b in zip(args_A, args_B)]
        rhs = Add(*args)
    else:
        args_B = B.of(Transpose[BlockMatrix])
        rhs = BlockMatrix(*[MatMul(arg, A.T).simplify() for arg in args_B]).T    
    
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import discrete, algebra

    a = Symbol.a(integer=True, positive=True)
    b = Symbol.b(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    C = Symbol.C(shape=(m, n), complex=True)
    A = Symbol.A(shape=(a, m), complex=True)
    B = Symbol.B(shape=(b, m), complex=True)
    Eq << apply(BlockMatrix(A, B) @ C)

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.to.lamda)

    i = Symbol.i(domain=Range(0, a + b))    
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], i)
    
    j = Symbol.j(domain=Range(0, n))    
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], j)


if __name__ == '__main__':
    run()
