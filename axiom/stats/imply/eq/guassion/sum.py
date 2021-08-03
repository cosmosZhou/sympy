from util import *


@apply
def apply(x0, x1):
    pspace0 = pspace(x0)
    pspace1 = pspace(x1)
    mean0, std0 = pspace0.distribution.of(NormalDistribution)
    mean1, std1 = pspace1.distribution.of(NormalDistribution)

    Y = Symbol.y(distribution=NormalDistribution(mean0 + mean1, sqrt(std0 * std0 + std1 * std1)))
    y = pspace(Y).symbol

    return Equal(Probability(Equal(x0 + x1, y)), Probability(Equal(Y, y)).doit())


@prove
def prove(Eq):
    from axiom import stats, algebra

    mu0, mu1 = Symbol(real=True)

    sigma0, sigma1 = Symbol(positive=True)

    x0 = Symbol.x0(distribution=NormalDistribution(mu0, sigma0))
    x1 = Symbol.x1(distribution=NormalDistribution(mu1, sigma1))

    Eq << apply(x0, x1)

    Eq << Eq[0].lhs.this.doit(evaluate=False)

    Eq << Eq[-1].this.rhs.find(Probability).doit()

    Eq << Eq[-1].this.rhs.find(Probability).doit()

    Eq << Eq[-1].this.rhs.find(Integral, Integral).doit()

    Eq << stats.imply.eq.guassion.quadratic.apply(Eq[-1].rhs.args[-1])

    Eq << Eq[-2].this.rhs.subs(Eq[-1])

    Eq << Eq[0].this.lhs.subs(Eq[-1])

    Eq << Eq[-1] / Eq[-1].rhs

    Eq << Eq[-1].apply(algebra.eq.given.eq.log)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.rhs.ratsimp()


# https://www.asmeurer.com/blog/
if __name__ == '__main__':
    run()

