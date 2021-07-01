from util import *


@apply
def apply(X, Y):
    i = Symbol.i(integer=True)

    y = pspace(Y).symbol
    k = Y.distribution.of(ChiSquaredDistribution)
    
    return Equal(Probability(Equal(Sum[i:k](X[i] * X[i]), y)), Probability(Equal(Y, y)).doit())


@prove
def prove(Eq):
    from axiom import stats
    i = Symbol.i(integer=True, nonnegative=True)
    X = Symbol.X(shape=(oo,), distribution=NormalDistribution(0, 1))

    k = Symbol.k(integer=True, positive=True)
    Y = Symbol.Y(distribution=ChiSquaredDistribution(k))

    Eq << apply(X, Y)

    Eq << stats.chiSquared.induct.apply(Symbol.Y(Lamda[k](Sum[i:k](X[i] * X[i]))), Y)

    Eq << Eq[-1].this.lhs.args[0].args[0].definition


# https://www.asmeurer.com/blog/
if __name__ == '__main__':
    run()
