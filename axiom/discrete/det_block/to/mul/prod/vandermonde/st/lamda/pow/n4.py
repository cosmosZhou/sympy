from util import *


@apply
def apply(self):
    ((r, j), j_limit), ((S[j], (S[r], S[j])), S[j_limit]), ((S[j], (S[r], S[j])), S[j_limit]), ((S[j], (S[r], S[j])), S[j_limit]), ((S[j], i), S[j_limit], (S[i], S[0], n)) = self.of(Det[BlockMatrix[Lamda[Pow], Lamda[Symbol * Pow], Lamda[Symbol ** 2 * Pow], Lamda[Symbol ** 3 * Pow], Lamda[Pow]]])

    S[j], S[0], S[n + 4:n > 0] = j_limit
    #Product[j:4](factorial(j))
    return Equal(self, 12 * r ** Binomial(4, 2) * (1 - r) ** (4 * n) * Product[j:n](factorial(j)))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    r = Symbol(real=True)
    n = Symbol(integer=True, positive=True)
    i, j = Symbol(integer=True)
    Eq << apply(Det(BlockMatrix([Lamda[j:n + 4](r ** j), Lamda[j:n + 4](j * r ** j), Lamda[j:n + 4](j ** 2 * r ** j), Lamda[j:n + 4](j ** 3 * r ** j), Lamda[j:n + 4, i:n](j ** i)])))

    #reference:
    #http://localhost/sympy/axiom.php?module=discrete.det_block.to.mul.prod.vandermonde.st.lamda.pow.n3
    j, i = Eq[0].lhs.arg.args[-1].variables
    E = Lamda[j:n + 4, i:n + 4]((-1) ** (j - i) * binomial(j, i))
    Eq << (Eq[0].lhs.arg @ E).this.apply(discrete.matmul.to.block)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].find(Lamda[Sum, Tuple[2]]).this().expr.simplify()

    Eq << Eq[-1].this.rhs.expr.apply(discrete.sum_binom.to.mul.stirling2, simplify=None)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Lamda[Sum, Tuple])().expr.simplify()

    Eq << Eq[-1].this.rhs.args[1]().expr.simplify()

    Eq << Eq[-1].this.rhs.args[2]().expr.simplify()

    Eq << Eq[-1].this.rhs.args[3]().expr.simplify()

    Eq.eq_block = Eq[-1].this.find(Sum).apply(discrete.sum_binom.to.pow.Newton)

    Eq << Eq.eq_block.rhs.args[1].expr.this.find(Pow).apply(algebra.pow.to.mul.split.exponent, simplify=None)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.mul)

    Eq << Eq[-1].this.rhs.find(Sum).expr.apply(algebra.mul.simplify.pow.mul.base)

    Eq << Eq[-1].this.rhs.find(Sum).apply(discrete.sum_binom.to.mul.Newton)

    Eq << Eq[-1].this.rhs.args[-1].apply(algebra.pow.to.mul.neg)

    Eq.eq_block = Eq.eq_block.subs(Eq[-1])

    Eq << Eq.eq_block.rhs.args[2].expr.this.find(Pow).apply(algebra.pow.to.mul.split.exponent, simplify=None)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.mul)

    Eq << Eq[-1].this.rhs.find(Sum).expr.apply(algebra.mul.simplify.pow.mul.base)

    Eq << Eq[-1].this.rhs.find(Sum).apply(discrete.sum_binom.to.mul.Newton.deux)

    Eq << Eq[-1].this.find(Add ** Add).apply(algebra.pow.to.mul.neg)

    Eq.eq_block = Eq.eq_block.subs(Eq[-1])

    Eq << Eq.eq_block.rhs.args[3].expr.this.find(Pow).apply(algebra.pow.to.mul.split.exponent, simplify=None)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.mul)

    Eq << Eq[-1].this.rhs.find(Sum).expr.apply(algebra.mul.simplify.pow.mul.base)

    Eq << Eq[-1].this.rhs.find(Sum).apply(discrete.sum_binom.to.mul.Newton.trois)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Add ** Add).apply(algebra.pow.to.mul.neg)

    Eq << Eq[-1].this.find((1 - Symbol) ** Add).apply(algebra.pow.to.mul.neg)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.mul)

    Eq << Eq.eq_block.subs(Eq[-1])

    Eq << ShiftMatrix(n + 4, 3, n + 3) @ Eq[-1]

    Eq << ShiftMatrix(n + 4, 2, n + 2) @ Eq[-1]

    Eq << ShiftMatrix(n + 4, 1, n + 1) @ Eq[-1]

    Eq << ShiftMatrix(n + 4, 0, n) @ Eq[-1]

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.lamda.to.block.split, n, axis=1)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.lamda.to.block.split, n)

    Eq << Eq[-1].this.rhs.args[2].apply(algebra.lamda.to.block.split, n)

    Eq << Eq[-1].this.rhs.args[3].apply(algebra.lamda.to.block.split, n)

    Eq << Eq[-1].this.rhs.args[4].apply(algebra.lamda.to.block.split, n)

    Eq << Eq[-1].this.rhs.args[0].args[1].apply(algebra.lamda.doit.inner)

    Eq << Eq[-1].this.rhs.args[0].args[1]().expr.simplify()

    Eq << Eq[-1].this.rhs.args[1].args[1].apply(algebra.lamda.to.matrix)

    Eq << Eq[-1].this.rhs.args[2].args[1].find(Lamda).apply(algebra.lamda.to.matrix)

    Eq << Eq[-1].this.rhs.args[3].args[1].find(Lamda).apply(algebra.lamda.to.matrix)

    Eq << Eq[-1].this.rhs.args[4].args[1].find(Lamda).apply(algebra.lamda.to.matrix)

    Eq << Eq[-1].this.find(Mul[Matrix]).apply(discrete.mul.to.matrix)

    Eq << Eq[-1].this.find(Mul[Matrix]).apply(discrete.mul.to.matrix)

    Eq << Eq[-1].this.find(Mul[Matrix]).apply(discrete.mul.to.matrix)

    Eq << discrete.eq.imply.eq.det.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(discrete.det.to.mul)

    Eq << Eq[-1].this.rhs.apply(discrete.det_block.to.mul)

    Eq << Eq[-1].this.find(Add ** Mul).apply(algebra.pow.to.mul.neg)

    


if __name__ == '__main__':
    run()
# created on 2022-07-11
