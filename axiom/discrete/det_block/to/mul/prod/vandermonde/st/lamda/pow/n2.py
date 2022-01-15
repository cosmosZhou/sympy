from util import *


@apply
def apply(self):
    ((r, j), j_limit), ((S[j], (S[r], S[j])), S[j_limit]), ((S[j], i), S[j_limit], (S[i], S[0], n)) = self.of(Det[BlockMatrix[Lamda[Pow], Lamda[Symbol * Pow], Lamda[Pow]]])

    S[j], S[0], S[n + 2:n > 0] = j_limit

    return Equal(self, r * (1 - r) ** (2 * n) * Product[i:n](factorial(i)))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    r = Symbol(real=True)
    n = Symbol(integer=True, positive=True)
    i, j = Symbol(integer=True)
    Eq << apply(Det(BlockMatrix([Lamda[j:n + 2](r ** j), Lamda[j:n + 2](j * r ** j), Lamda[j:n + 2, i:n](j ** i)])))

    j, i = Eq[0].lhs.arg.args[2].variables
    E = Lamda[j:n + 2, i:n + 2]((-1) ** (j - i) * binomial(j, i))
    Eq << (Eq[0].lhs.arg @ E).this.apply(discrete.matmul.to.block)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].find(Lamda[Sum, Tuple[2]]).this().expr.simplify()

    _i = i.copy(domain=Range(n))
    _j = j.copy(domain=Range(n + 1))
    Eq << discrete.stirling2.to.mul_sum.apply(i, j)

    Eq << Eq[-1] * factorial(j)

    Eq << Eq[-1].reversed

    Eq << Eq[-4].subs(Eq[-1])

    Eq << Eq[4].subs(Eq[-1])

    Eq << Eq[-1].find(Lamda[Sum, Tuple]).this().expr.simplify()

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Sum).apply(discrete.sum_binom.to.pow.Newton)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.mul)

    Eq << Eq[-1].this.find(Sum).expr.powsimp()

    Eq << Eq[-1].this.find(Lamda[Mul[Sum]])().find(Sum).simplify()

    Eq << Eq[-1].this.find(Sum).apply(discrete.sum_binom.to.mul.Newton)

    Eq << Eq[-1].this.find(Add ** Add).apply(algebra.pow.to.mul.neg)

    Eq << ShiftMatrix(n + 2, 1, n + 1) @ Eq[-1]

    Eq << ShiftMatrix(n + 2, 0, n) @ Eq[-1]

    Eq << discrete.eq.imply.eq.det.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(discrete.det.to.mul)

    Eq << Eq[-1].this.rhs.find(Lamda).apply(algebra.lamda.to.transpose.block, n)

    Eq << Eq[-1].this.find(Lamda[Factorial * Stirling])().expr.args[1].simplify()

    Eq << Eq[-1].this.find(Lamda[Pow[Add]]).apply(algebra.lamda.to.block.split, n)

    Eq << Eq[-1].this.rhs.find(Lamda[2]).apply(algebra.lamda.to.matrix)

    Eq << Eq[-1].this.find(Mul[Lamda[Mul]]).apply(algebra.mul.to.lamda)

    Eq << Eq[-1].this.find(Lamda[Mul[Pow[Add]]]).apply(algebra.lamda.to.block.split, n)

    Eq << Eq[-1].this.rhs.find(Lamda[2]).apply(algebra.lamda.to.matrix)

    Eq << Eq[-1].this.rhs.apply(discrete.det_block.to.mul)

    Eq << Eq[-1].this.find(Mul[Add ** Add]).powsimp()

    Eq << Eq[-1].this.find(Add[Mul]).apply(algebra.add.to.mul)

    Eq << Eq[-1].this.find(Add ** Mul).apply(algebra.pow.neg)





if __name__ == '__main__':
    run()
# created on 2021-11-23
# updated on 2021-11-25