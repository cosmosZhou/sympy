from util import *


@apply
def apply(self):
    (((j, i), (x, S[j])), (S[j], S[0], m), (S[i], S[0], d)), (((S[-x], S[j - i]), (S[j], S[i])), (S[j], S[0], S[d]), (S[i], S[0], S[m])) = self.of(Det[Lamda[Pow * Pow] @ Lamda[Pow * Binomial]])
    return Equal(self, x ** Binomial(d, 2) * Product[i:d](factorial(i)))


@prove
def prove(Eq):
    d, m = Symbol(integer=True, positive=True)
    i, j = Symbol(integer=True)
    x = Symbol(real=True)
    Eq << apply(Det(Lamda[j:m, i:d](j ** i * x ** j) @ Lamda[j:d, i:m](Binomial(j, i) * (-x) ** (j - i))))

    


if __name__ == '__main__':
    run()
# created on 2022-01-15
