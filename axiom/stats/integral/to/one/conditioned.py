from util import *


@apply
def apply(self):
    ((X, x), (Y, y)), (_x, *_) = self.of(Integral[Probability[Conditioned[Equal, Equal]]])
    assert x == _x
    
    return Equal(self, 1)    


@prove
def prove(Eq):
    from axiom import stats

    x = Symbol.x(integer=True, random=True)
    y = Symbol.y(integer=True, random=True)
    x_ = Symbol.x(integer=True)
    Eq << apply(Integral[x_](Probability(x | y)))

    Eq << Eq[-1].this.lhs.function.apply(stats.probability.to.mul)

    Eq << Eq[-1].this.find(Integral).apply(stats.integral.to.probability)


if __name__ == '__main__':
    run()