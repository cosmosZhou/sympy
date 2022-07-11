from util import *


@apply
def apply(self):
    (((j, i), (x, S[j])), (S[j], S[0], m), (S[i], S[0], d)), (((S[-x], S[j - i]), (S[j], S[i])), (S[j], S[0], S[d]), (S[i], S[0], S[m])) = self.of(Lamda[Pow * Pow] @ Lamda[Pow * Binomial])
    assert d <= m
    from sympy.functions.combinatorial.numbers import Stirling
    return Equal(self, Lamda[j:d, i:d](x ** j * factorial(j) * Stirling(i, j)))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    m = Symbol(integer=True, positive=True)
    d = Symbol(domain=Range(m))
    i, j = Symbol(integer=True)
    x = Symbol(real=True)
    Eq << apply(Lamda[j:m, i:d](j ** i * x ** j) @ Lamda[j:d, i:m](Binomial(j, i) * (-x) ** (j - i)))

    Eq << Eq[-1].this.lhs.apply(discrete.matmul.to.lamda, simplify=None)

    Eq << Eq[-1].this.find((-Symbol) ** Add).apply(algebra.pow.to.mul.neg, simplify=None)

    Eq << Eq[-1].this.lhs().find(Sum).simplify()

    Eq << Eq[-1].this.find(Sum).apply(discrete.sum_binom.to.mul.stirling2)

    


if __name__ == '__main__':
    run()
# created on 2022-01-18
