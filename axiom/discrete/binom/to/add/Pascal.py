from util import *


@apply
def apply(self):
    n, k = self.of(Binomial)
    return Equal(self, binomial(n - 1, k) + binomial(n - 1, k - 1))


@prove
def prove(Eq):
    from axiom import discrete

    n = Symbol(integer=True, positive=True)
    k = Symbol(domain=Range(1, n))
    Eq << apply(Binomial(n, k))

    Eq << Eq[-1].this.lhs.apply(discrete.binom.to.mul)

    Eq << Eq[-1].this.find(binomial).apply(discrete.binom.to.mul)

    Eq << Eq[-1].this.find(binomial).apply(discrete.binom.to.mul)

    Eq << Eq[-1].this.find(Factorial).apply(discrete.factorial.to.mul)

    Eq << Eq[-1] / factorial(n - 1)

    Eq << Eq[-1] * factorial(k)

    Eq << Eq[-1] * factorial(n - k)

    Eq << Eq[-1].this.find(Factorial).apply(discrete.factorial.to.mul)

    Eq << Eq[-1].this.rhs.ratsimp()

    Eq << Eq[-1].this.find(Factorial).apply(discrete.factorial.to.mul)

    


if __name__ == '__main__':
    run()
# created on 2020-09-28
# updated on 2022-01-15
