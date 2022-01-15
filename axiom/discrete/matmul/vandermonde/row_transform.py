from util import *


@apply
def apply(self):
    (expr, (j, S[0], m), (i, S[0], m_d)), (((x, S[i]), (delta, S[j])), (S[j], S[0], n), (S[i], S[0], S[m])) = self.of(Lamda[(-Expr) ** Add * Binomial] @ Lamda[Pow * Pow])
    (λ, (d, _i, _j)), (S[d], S[j - i]) = expr
    if _i != i:
        _i, _j = _j, _i
    assert _i == i and _j == -j
    assert m_d == m - d

    delta -= i
    assert not delta._has(i)
    h = self.generate_var(integer=True, var='h')
    return Equal(self, Lamda[j:n, i:m - d]((i + delta) ** j * x ** i) @ Lamda[j:n, i:n](binomial(j, i) * Sum[h:d + 1](binomial(d, h) * (-λ) ** (d - h) * x ** h * h ** (j - i))))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n, m = Symbol(integer=True, positive=True)
    d = Symbol(integer=True, nonnegative=True)
    i, j = Symbol(integer=True)
    λ, delta, x = Symbol(real=True)
    Eq << apply(Lamda[j:m, i:m - d](binomial(d, j - i) * (-λ) ** (d + i - j)) @ Lamda[j:n, i:m]((i + delta) ** j * x ** i))

    Eq << Eq[-1].this.lhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.lamda)

    i = Symbol(domain=Range(m - d))
    j = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], [i, j])

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.sum_sum.limits.swap)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.sum.limits.subs.offset, -i)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.find(Mul[~Sum]).apply(discrete.sum_binom.to.pow.Newton)




if __name__ == '__main__':
    run()
# created on 2022-01-15
