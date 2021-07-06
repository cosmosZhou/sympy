from util import *


@apply
def apply(x0, x1):    
    pspace0 = pspace(x0)
    pspace1 = pspace(x1)
    
    lamda0 = pspace0.distribution.of(PoissonDistribution)
    lamda1 = pspace1.distribution.of(PoissonDistribution)

    Y = Symbol.y(distribution=PoissonDistribution(lamda0 + lamda1))
    y = pspace(Y).symbol

    return Equal(Probability(Equal(x0 + x1, y)), Probability(Equal(Y, y)).doit())


@prove
def prove(Eq):
    from axiom import discrete
    lamda0 = Symbol.lamda0(positive=True)
    lamda1 = Symbol.lamda1(positive=True)

    x0 = Symbol.x0(distribution=PoissonDistribution(lamda0))
    x1 = Symbol.x1(distribution=PoissonDistribution(lamda1))

    Eq << apply(x0, x1)

    Eq << Eq[0].this.lhs.this.doit(evaluate=False)

    Eq << Eq[-1].this.lhs.powsimp()

    y = Eq[0].lhs.arg.rhs
    Eq << Eq[-1] * factorial(y)

    Eq << discrete.combinatorics.binomial.theorem.apply(lamda0, lamda1, y)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(binomial).apply(discrete.binomial.to.mul)


if __name__ == '__main__':
    run()