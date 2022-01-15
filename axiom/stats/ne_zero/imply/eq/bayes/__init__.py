from util import *


@apply
def apply(eq, *expr):
    given_probability = eq.of(Unequal[0])
    cond = given_probability.of(Probability)

    condition = And(*(Equal(var, pspace(var).symbol) for var in expr))
    self = Probability(cond & condition)
    given_marginal_prob = Probability(condition, given=cond)
    return Equal(self, given_probability * given_marginal_prob)


@prove
def prove(Eq):
    from axiom import stats

    x, y = Symbol(real=True, random=True)
    Eq << apply(Unequal(Probability(y), 0), x)

    Eq << Eq[-1].this.find(Probability[Conditioned]).apply(stats.probability.to.mul)


if __name__ == '__main__':
    run()

from . import conditioned
from . import cond
# created on 2020-12-09
