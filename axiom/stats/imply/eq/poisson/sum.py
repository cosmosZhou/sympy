from util import *


@apply
def apply(x0, x1):
    pspace0 = pspace(x0)
    pspace1 = pspace(x1)

    lamda0 = pspace0.distribution.of(PoissonDistribution)
    lamda1 = pspace1.distribution.of(PoissonDistribution)

    Y = Symbol(distribution=PoissonDistribution(lamda0 + lamda1))
    y = pspace(Y).symbol

    return Equal(Probability(Equal(x0 + x1, y)), Probability(Equal(Y, y)).doit())


@prove
def prove(Eq):
    from axiom import algebra, discrete

    lamda0, lamda1 = Symbol(positive=True)
    x0 = Symbol(distribution=PoissonDistribution(lamda0))
    x1 = Symbol(distribution=PoissonDistribution(lamda1))
    Eq << apply(x0, x1)

    Eq << Eq[0].this.lhs.doit(evaluate=False)

    Eq << Eq[-1].this.lhs.powsimp()

    y = Eq[0].lhs.arg.rhs
    Eq << Eq[-1] * factorial(y)

    Eq << Eq[-1].this.rhs.apply(discrete.pow.to.sum.binom.Newton)

    Eq << Eq[-1].this.find(binomial).apply(discrete.binom.to.mul)


if __name__ == '__main__':
    run()
# created on 2021-07-18
# updated on 2021-11-25
