from util import *


@apply
def apply(n, k):
    return Equal(Binomial(n, k) / n, Binomial(n - 1, k) / (n - k))


@prove
def prove(Eq):
    from axiom import discrete

    n = Symbol(integer=True, positive=True)
    k = Symbol(domain=Range(n))
    Eq << apply(n, k)

    Eq << Eq[-1].this.find(binomial).apply(discrete.binom.to.mul)

    Eq << Eq[-1].this.find(binomial).apply(discrete.binom.to.mul)

    #Eq << Eq[-1] * Factorial(k)

    Eq << Eq[-1].this.find(Factorial).apply(discrete.factorial.to.mul)

    Eq << Eq[-1].this.find(Factorial).apply(discrete.factorial.to.mul)


if __name__ == '__main__':
    run()
# created on 2020-10-07
