from util import *


@apply
def apply(self):
    (((j, i), (x, S[j])), (S[j], S[0], m), (S[i], S[0], d)), (((S[-x], S[j - i]), (S[j], S[i])), (S[j], S[0], S[d]), (S[i], S[0], S[m])) = self.of(Det[Lamda[Pow * Pow] @ Lamda[Pow * Binomial]])
    assert d <= m
    return Equal(self, x ** Binomial(d, 2) * Product[i:d](factorial(i)))


@prove
def prove(Eq):
    from axiom import discrete

    m = Symbol(integer=True, positive=True)
    d = Symbol(domain=Range(m))
    i, j = Symbol(integer=True)
    x = Symbol(real=True)
    Eq << apply(Det(Lamda[j:m, i:d](j ** i * x ** j) @ Lamda[j:d, i:m](Binomial(j, i) * (-x) ** (j - i))))

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul_lamda.to.lamda.stirling2.vandermonde)

    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq[-1].this.find(Binomial).apply(discrete.binom.to.mul.fallingFactorial.doit)

    Eq << Eq[-1].this.rhs.find(Mul).expand()
    


if __name__ == '__main__':
    run()
# created on 2022-01-15
# updated on 2022-01-18
