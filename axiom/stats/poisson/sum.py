from util import *


@apply
def apply(x0, x1):
    from sympy.stats.rv import PDF
    assert x0.is_random and x1.is_random
    pspace0 = pspace(x0)
    pspace1 = pspace(x1)
    if not pspace0.is_SingleDiscretePSpace or not pspace1.is_SingleDiscretePSpace:
        return
    distribution0 = pspace0.distribution
    distribution1 = pspace1.distribution
    if not isinstance(distribution0, PoissonDistribution) or not isinstance(distribution1, PoissonDistribution):
        return

    Y = Symbol.y(distribution=PoissonDistribution(distribution0.lamda + distribution1.lamda))
    y = pspace(Y).symbol

    return Equal(PDF(x0 + x1)(y), PDF(Y)(y).doit())


@prove
def prove(Eq):
    from axiom import discrete
    assert NonnegativeIntegers.is_extended_negative == False
    assert NonnegativeIntegers.is_extended_nonnegative

    lamda0 = Symbol.lamda0(positive=True)
    lamda1 = Symbol.lamda1(positive=True)

    x0 = Symbol.x0(distribution=PoissonDistribution(lamda0))
    x1 = Symbol.x1(distribution=PoissonDistribution(lamda1))

    Eq << apply(x0, x1)

    Eq << Eq[0].this.lhs.this.doit(evaluate=False)

    Eq << Eq[-1].this.lhs.powsimp()

    y = Eq[0].lhs.symbol
    Eq << Eq[-1] * factorial(y)

    Eq << discrete.combinatorics.binomial.theorem.apply(lamda0, lamda1, y)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(binomial).apply(discrete.binomial.to.mul)


if __name__ == '__main__':
    run()
