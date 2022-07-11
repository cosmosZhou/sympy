from util import *


@apply
def apply(self):
    ((X, x), (Y, y)), (_x, *_) = self.of(Sum[Probability[Conditioned[Equal, Equal]]])
    assert x == _x

    return Equal(self, 1)


@prove
def prove(Eq):
    from axiom import stats

    x, y = Symbol(integer=True, random=True)
    x_ = Symbol('x', integer=True)
    Eq << apply(Sum[x_](Probability(x | y)))

    Eq << Eq[-1].this.lhs.expr.apply(stats.probability.to.mul)

    Eq << Eq[-1].this.find(Sum).apply(stats.sum.to.probability)


if __name__ == '__main__':
    run()
# created on 2021-07-18
