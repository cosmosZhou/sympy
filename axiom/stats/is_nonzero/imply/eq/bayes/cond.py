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

    X = Symbol.X(real=True, random=True)
    x = Symbol.x(real=True)
    Y = Symbol.Y(real=True, random=True)
    y = Symbol.y(real=True)
    Eq << apply(Unequal(Probability(Equal(X, x)), 0), cond=Equal(Y, y))
    
    X_ = pspace(X).symbol
    Eq << Eq[0].subs(x, X_)
    
    Eq << stats.is_nonzero.imply.eq.bayes.apply(Eq[-1], Y)
    
    Eq << Eq[-1].subs(X_, x)
    
    Y_ = pspace(Y).symbol
    Eq << Eq[-1].subs(Y_, y)


if __name__ == '__main__':
    run()
