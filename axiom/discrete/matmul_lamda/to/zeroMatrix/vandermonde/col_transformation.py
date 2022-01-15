from util import *


@apply
def apply(self):
    (((_x, _j), (delta, _i)), (j, S[0], m), (i, S[0], d)), (((x, (S[d], S[-i], S[j])), (S[d], S[i - j])), (S[j], S[0], S[m - d]), (S[i], S[0], S[m])) = self.of(Lamda[Pow * Pow] @ Lamda[(-Symbol) ** Add * Binomial])
    if _x != x:
        _x, _j, delta, _i = delta, _i, _x, _j
        
    assert _x == x
    assert _j == j
    assert _i == i
         
    delta -= j
    assert not delta._has(j)    
    return Equal(self, ZeroMatrix(d, m - d))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    m = Symbol(integer=True, positive=True)
    d = Symbol(integer=True, nonnegative=True)
    i, j = Symbol(integer=True)
    delta, x = Symbol(real=True)
    Eq << apply(Lamda[j:m, i:d]((j + delta) ** i * x ** j) @ Lamda[j:m - d, i:m](binomial(d, i - j) * (-x) ** (d + j - i)))

    Eq << Eq[-1].this.lhs.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.find(Pow[-Symbol]).apply(algebra.pow.to.mul.neg)

    #j < m - d
    #k <= d + j < d + (m - d) = m
    #k < m
    Eq << Eq[-1].this.lhs().expr.simplify()

    Eq << Eq[-1].this.find(Sum).apply(discrete.sum_binom.to.mul.difference)
    Eq << Eq[-1].this.lhs().find(Difference).apply(discrete.difference.to.zero)

    
    


if __name__ == '__main__':
    run()
# created on 2021-11-30
# updated on 2021-12-01