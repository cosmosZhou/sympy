from util import *


@apply
def apply(self):
    (((j, i), (r, S[j])), (S[j], S[0], m), (S[i], S[0], d)), ((S[j], S[i]), (S[j], S[0], S[m]), (S[i], S[0], S[m - d])) = self.of(Det[BlockMatrix[Lamda[Pow * Pow], Lamda[Pow]]])
    assert m > d
    return Equal(self, r ** Binomial(d, 2) * (1 - r) ** (d * (m - d)) * Product[i:d](factorial(i)) * Product[i:m - d](factorial(i)))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    λ = Symbol(real=True)
    d = Symbol(integer=True, positive=True)
    m = Symbol(domain=Range(d + 1, oo))
    i, j = Symbol(integer=True)
    Eq << apply(Det(BlockMatrix([Lamda[j:m, i:d](j ** i * λ ** j), Lamda[j:m, i:m - d](j ** i)])))

    E = BlockMatrix(Lamda[j:d, i:m]((-λ) ** (j - i) * binomial(j, i)).T, Lamda[j:m - d, i:m]((-λ) ** (d + j - i) * binomial(d, i - j)).T).T
    Eq << (Eq[0].lhs.arg @ E).this.apply(discrete.matmul.to.block)

    Eq << Eq[-1].this.rhs.find(Mul[Lamda]).apply(algebra.mul.to.lamda, simplify=None)

    Eq << Eq[-1].this.rhs.find(Mul[Lamda]).apply(algebra.mul.to.lamda, simplify=None)

    Eq << Eq[-1].this.rhs.args[0].args[1].apply(discrete.matmul_lamda.to.zeroMatrix.vandermonde.col_transformation)

    Eq << Eq[-1].this.find(BlockMatrix[1]).apply(algebra.block.to.lamda.piece)

    Eq << Eq[-1].this.find(Binomial[Add]).apply(discrete.binom.complement)

    Eq << discrete.eq.imply.eq.det.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(discrete.det.to.mul.deux)

    Eq << Eq[-1].this.rhs.apply(discrete.det_block.to.mul)

    Eq << Eq[-1].this.lhs.args[1].doit()

    Eq << Eq[-1].this.find(Det[MatMul]).apply(discrete.det_matmul.to.mul.prod.vandermonde.col_transform.st.one)

    Eq << Eq[-1].this.find(Det[MatMul]).apply(discrete.det_matmul_lamda.to.mul.prod.vandermonde)

    


if __name__ == '__main__':
    run()
# created on 2021-11-25
# updated on 2022-07-11
