from util import *


@apply
def apply(eq, *, cond=None):
    given_probability = eq.of(Unequal[0])
    given = given_probability.of(Probability)
    assert given.is_Equal
    self = Probability(given & cond)
    given_marginal_prob = Probability(cond, given=given)
    return Equal(self, given_probability * given_marginal_prob)


@prove
def prove(Eq):
    from axiom import stats, algebra

    X, Y = Symbol(real=True, random=True)
    x, y = Symbol(real=True)
    Eq << apply(Unequal(Probability(Equal(X, x)), 0), cond=Equal(Y, y))

    X_ = pspace(X).symbol
    Eq << Eq[0].subs(x, X_)

    Eq << stats.ne_zero.imply.eq.bayes.apply(Eq[-1], Y)

    Eq << Eq[-1].subs(X_, x)

    Y_ = pspace(Y).symbol
    Eq << Eq[-1].subs(Y_, y)


if __name__ == '__main__':
    run()
# created on 2021-07-22
