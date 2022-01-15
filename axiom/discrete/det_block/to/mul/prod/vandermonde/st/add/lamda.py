from util import *


@apply
def apply(self):
    ((r, j1), (j, S[0], n)), ((S[j + 1], i1), (S[j], S[0], S[n]), (i, S[0], S[n - 1])) = self.of(Det[BlockMatrix[1 - Lamda[Pow], Lamda[Pow]]])

    assert j1 == j + 1
    assert i1 == i + 1

    return Equal(self, (1 - r) ** n * Product[i:n](factorial(i)))


@prove
def prove(Eq):
    from axiom import discrete, algebra, sets

    r = Symbol(real=True)
    n = Symbol(integer=True, positive=True)
    n = Symbol(domain=Range(2, oo))
    i, j = Symbol(integer=True)
    Eq << apply(Det(BlockMatrix([1 - Lamda[j:n](r ** (j + 1)), Lamda[j:n, i:n - 1]((j + 1) ** (i + 1))])))

    Eq << discrete.det_block.to.mul.prod.vandermonde.st.lamda.pow.apply(Det(BlockMatrix([Lamda[j:n + 1](r ** j), Lamda[j:n + 1, i:n](j ** i)])))

    Eq << Eq[-1].lhs.arg.this.args[1].apply(discrete.lamda.to.block.split, 1)

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], SwapMatrix(n + 1, 0, 1))

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.oneMatrix.to.block, 1)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.lamda.to.block.split, 1)

    Eq << Eq[-1].this.rhs.args[2].apply(algebra.lamda.to.transpose.block, 1)

    Eq << Eq[-1].this.find(Lamda[Zero ** Add])().expr.simplify()

    Eq << Eq[-1] @ MulMatrix(n + 1, 0, -1)

    Eq.matmul = Eq[-1] @ (Identity(n + 1) + Lamda[j:n + 1, i:n + 1]((1 - KroneckerDelta(j, 0)) * KroneckerDelta(i, 0)))

    Eq << algebra.add.to.lamda.apply(Eq.matmul.rhs.args[1])

    Eq << Eq[-1].this.rhs.apply(algebra.lamda.to.block.pop_front)

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.oneMatrix.to.block, 1)

    Eq << Eq[-1].this.rhs.args[0].args[1].apply(algebra.oneMatrix.to.block, 1)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.lamda.to.transpose.block, 1)

    Eq << Eq[-1].this.rhs.args[1].args[1].apply(algebra.lamda.to.block.split, 1, axis=1)

    Eq << Eq.matmul.this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.block, deep=True)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.sum)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.sum)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.sum)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.add)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.sum)

    Eq << Eq[-1].this.find(Sum).expr.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.find(Sum).expr.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.find(Element).apply(sets.el.sub, 1)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.find(Sum).expr.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Element).apply(sets.el.sub, 1)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.find(Sum).expr.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Element).apply(sets.el.sub, 1)

    Eq << Eq[-1].this.rhs.apply(algebra.add_block.to.block)

    Eq << Eq[-1].this.find(Add[BlockMatrix]).apply(algebra.add.to.block)

    Eq << Eq[-1].this.find(Add[BlockMatrix]).apply(algebra.add.to.block)

    Eq << MulMatrix(n + 1, 1, -1) @ (MulMatrix(n + 1, 0, -1) @ Eq[-1])

    Eq << discrete.eq.imply.eq.det.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(discrete.det.to.mul).reversed.subs(Eq[1])

    Eq << Eq[0].find(1 - Lamda).this.apply(algebra.add.to.lamda)

    Eq << Eq[-1].this.rhs.apply(algebra.lamda.to.block.pop_front)

    Eq << Eq[-1].this.find(Lamda[Add]).apply(algebra.lamda.to.add)

    Eq << Eq[-4].subs(Eq[-1].reversed)

    Eq << Eq[0].find(Lamda[Tuple[2]]).this.apply(algebra.lamda.to.transpose.block, 1)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << ZeroMatrix(n).this.apply(algebra.zeroMatrix.to.block, 1)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.lhs.apply(discrete.det_block.to.mul)

    
    


if __name__ == '__main__':
    run()
# created on 2020-10-14
# updated on 2022-01-15