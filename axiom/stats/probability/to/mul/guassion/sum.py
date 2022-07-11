from util import *


@apply
def apply(x0, x1):
    pspace0 = pspace(x0)
    pspace1 = pspace(x1)
    mean0, std0 = pspace0.distribution.of(NormalDistribution)
    mean1, std1 = pspace1.distribution.of(NormalDistribution)

    Y = Symbol(distribution=NormalDistribution(mean0 + mean1, sqrt(std0 * std0 + std1 * std1)))
    y = pspace(Y).symbol

    return Equal(Probability(Equal(x0 + x1, y)), Probability(Equal(Y, y)).doit())


@prove
def prove(Eq):
    from axiom import stats, calculus, algebra

    mu0, mu1 = Symbol(real=True)
    sigma0, sigma1 = Symbol(positive=True)
    x0 = Symbol(distribution=NormalDistribution(mu0, sigma0))
    x1 = Symbol(distribution=NormalDistribution(mu1, sigma1))
    Eq << apply(x0, x1)

    Eq << Eq[0].lhs.this.apply(stats.probability.to.derivative)

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.limits.separate)

    Eq << Eq[-1].this.rhs.find(Probability).doit()

    Eq << Eq[-1].this.rhs.find(Probability).doit()

    Eq << Eq[-1].this.find(LessEqual).apply(algebra.le.transport)

    Eq << Eq[-1].this.find(Integral, Integral).apply(calculus.integral.doit.bool)

    Eq << Eq[-1].this.find(Derivative).apply(calculus.derivative.to.integral)

    Eq << Eq[-1].this.find(Derivative).apply(calculus.derivative_integral.to.mul.derivative)

    Eq << Eq[-1].this.find(Derivative).doit()

    Eq << Eq[-1].this.find(Exp * Exp).apply(algebra.mul.to.exp)

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.to.mul.st.exp.quadratic)

    Eq << Eq[0].this.find(Add ** 2).apply(algebra.square.to.add)

    Eq << Eq[-1].this.find(Exp).arg.apply(algebra.mul.distribute)


if __name__ == '__main__':
    run()

# created on 2021-07-25
