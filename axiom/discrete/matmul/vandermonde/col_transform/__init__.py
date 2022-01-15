from util import *


@apply
def apply(self):
    (((x, j), (delta, i)), (S[j], S[0], m), (S[i], S[0], n)), (((λ, (d, S[-i], S[j])), (S[d], S[i - j])), (S[j], S[0], S[m - d]), (S[i], S[0], S[m])) = self.of(Lamda[Pow * Pow] @ Lamda[(-Expr) ** Add * Binomial])
    delta -= j
    assert not delta._has(j)
    h = self.generate_var(integer=True, var='h')
    return Equal(self, Lamda[j:n, i:n](binomial(i, j) * Sum[h:d + 1](binomial(d, h) * (-λ) ** (d - h) * x ** h * h ** (i - j))) @ Lamda[j:m - d, i:n]((j + delta) ** i * x ** j))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    n, m = Symbol(integer=True, positive=True)
    d = Symbol(integer=True, nonnegative=True)
    i, j = Symbol(integer=True)
    λ, delta, x = Symbol(real=True)
    Eq << apply(Lamda[j:m, i:n]((j + delta) ** i * x ** j) @ Lamda[j:m - d, i:m](binomial(d, i - j) * (-λ) ** (d + j - i)))

    Eq << Eq[-1].T

    Eq << Eq[-1].this.find(Mul[Lamda]).apply(algebra.mul.to.lamda, simplify=None)

    Eq << Eq[-1].this.lhs.apply(discrete.matmul.vandermonde.row_transform)

    Eq << Eq[-1].this.find(Mul[Lamda]).apply(algebra.mul.to.lamda, simplify=None)

    


if __name__ == '__main__':
    run()
# created on 2022-01-15

from . import st
