from util import *


@apply
def apply(self):
    (((x, j), (delta, i)), (S[j], S[0], m), (S[i], S[0], (S[m], d))), (((λ, (S[d], S[-i], S[j])), (S[d], S[i - j])), (S[j], S[0], S[m - d]), (S[i], S[0], S[m])) = self.of(Det[Lamda[Pow * Pow, Tuple[Expr - Expr]] @ Lamda[(-Expr) ** Add * Binomial]])
    delta -= j
    assert not delta._has(j)
    h = self.generate_var(integer=True, var='h')
    return Equal(self, x ** Binomial(m - d, 2) * (x - λ) ** (d * (m - d)) * Product[i:m - d](factorial(i)))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    m = Symbol(integer=True, positive=True)
    d = Symbol(integer=True, nonnegative=True)
    i, j = Symbol(integer=True)
    λ, delta, x = Symbol(real=True)
    Eq << apply(Det(Lamda[j:m, i:m - d]((j + delta) ** i * x ** j) @ Lamda[j:m - d, i:m](binomial(d, i - j) * (-λ) ** (d + j - i))))

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.vandermonde.col_transform)

    Eq << Eq[-1].this.lhs.apply(discrete.det.to.mul)

    Eq << Eq[-1].this.find(Sum).apply(discrete.sum_binom.to.pow.Newton)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.mul)

    Eq << Eq[-1].this.find(Det).apply(discrete.det_mul.to.mul.prod.st.lamda)

    Eq << Eq[-1].this.find(Product).apply(algebra.prod.to.pow.sum)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.mul.arithmetic_progression)

    Eq << Eq[-1].this.find(Det).apply(discrete.det_lamda.to.prod.vandermonde.st.linear)

    Eq << Eq[-1].this.find(Binomial).apply(discrete.binom.to.mul.fallingFactorial.doit)


if __name__ == '__main__':
    run()
# created on 2022-01-15

from . import st
