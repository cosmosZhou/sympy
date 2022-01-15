from util import *


@apply
def apply(self):
    ((delta, i), (j, S[0], m), (S[i], S[0], (S[m], d))), (((λ, (S[d], S[-i], S[j])), (S[d], S[i - j])), (S[j], S[0], S[m - d]), (S[i], S[0], S[m])) = self.of(Det[Lamda[Pow, Tuple[Expr - Expr]] @ Lamda[(-Expr) ** Add * Binomial]])
    delta -= j
    assert not delta._has(j)
    h = self.generate_var(integer=True, var='h')
    return Equal(self, (1 - λ) ** (d * (m - d)) * Product[i:m - d](factorial(i)))


@prove
def prove(Eq):
    from axiom import discrete

    m = Symbol(integer=True, positive=True)
    d = Symbol(integer=True, nonnegative=True)
    i, j = Symbol(integer=True)
    λ, delta, x = Symbol(real=True)
    Eq << apply(Det(Lamda[j:m, i:m - d]((j + delta) ** i) @ Lamda[j:m - d, i:m](binomial(d, i - j) * (-λ) ** (d + j - i))))

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.vandermonde.col_transform.st.one)

    Eq << Eq[-1].this.lhs.apply(discrete.det.to.mul)

    Eq << Eq[-1].this.find(Sum).apply(discrete.sum_binom.to.pow.Newton)

    Eq << Eq[-1].this.find(Det).apply(discrete.det_lamda.to.prod.vandermonde.st.linear)

    

    


if __name__ == '__main__':
    run()
# created on 2022-01-15
