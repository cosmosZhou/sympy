from util import *


@apply
def apply(pX, pY):
    pX.of(Probability[Conditioned])
    pY.of(Probability[Conditioned])
    from axiom.stats.imply.sum_ge_zero import KL
    return GreaterEqual(KL(pX, pY), 0)


@prove
def prove(Eq):
    from axiom import algebra, stats

    Y, X = Symbol(random=True, integer=True)
    Y_ = Symbol("Y'", random=True, integer=True)
    X_ = Symbol("X'", random=True, integer=True)
    y, x = Symbol(integer=True)
    Eq << apply(Probability(Equal(Y, y), given=Equal(X, x)), Probability(Equal(Y_, y), given=Equal(X_, x)))

    Eq << algebra.imply.ge.log.apply(Eq[0].find(Log).arg)

    Eq << algebra.ge.imply.ge.mul.apply(Eq[-1], Eq[0].find(Probability))

    Eq << algebra.ge.imply.ge.sum.apply(Eq[-1], (y,))

    Eq << Eq[-1].this.rhs.expr.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)
    Eq << Eq[-1].this.rhs.args[0].apply(stats.sum.to.one.conditioned)
    Eq << Eq[-1].this.rhs.find(Sum).apply(stats.sum.to.one.conditioned)


if __name__ == '__main__':
    run()
# created on 2021-07-19
