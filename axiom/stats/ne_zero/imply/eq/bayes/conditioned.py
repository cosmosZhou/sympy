from util import *


@apply
def apply(eq, *vars):
    given_probability = eq.of(Unequal[0])
    cond, given = given_probability.of(Probability[Conditioned])

    condition = And(*(Equal(var, pspace(var).symbol) for var in vars))
    self = Probability(cond & condition, given=given)
    given_marginal_prob = Probability(condition, given=cond & given)
    return Equal(self, given_probability * given_marginal_prob)


@prove
def prove(Eq):
    from axiom import stats, algebra

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Unequal(Probability(y | z), 0), x)

    Eq << stats.ne_zero.imply.ne_zero.condition.apply(Eq[0])

    Eq << stats.ne_zero.imply.eq.bayes.apply(Eq[-1], x, y)

    Eq.lhs = algebra.ne_zero.eq.imply.eq.div.apply(Eq[-2], Eq[-1])

    Eq << stats.ne_zero.imply.ne_zero.joint.apply(Eq[0])

    Eq << stats.ne_zero.imply.eq.bayes.apply(Eq[-1], x)

    Eq << algebra.ne_zero.eq.imply.eq.div.apply(Eq[-2], Eq[-1]).reversed

    Eq << stats.ne_zero.imply.eq.bayes.apply(Eq[2], y)

    Eq << algebra.ne_zero.eq.imply.eq.div.apply(Eq[2], Eq[-1]).reversed

    Eq << Eq[-1] * Eq[-3]

    Eq << Eq[-1].subs(Eq.lhs).reversed


if __name__ == '__main__':
    run()
# created on 2020-12-11
