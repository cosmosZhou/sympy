from util import *


@apply
def apply(given):
    (x, y), rhs = given.of(Equal[Conditioned])

    assert x == rhs

    return Equal(Probability(x, y), Probability(x) * Probability(y))


@prove
def prove(Eq):
    from axiom import stats

    x, y = Symbol(real=True, random=True)
    Eq << apply(Equal(x | y, x))

    Eq << stats.eq.imply.eq.probability.apply(Eq[0], simplify=False)

    Eq << Eq[-1].this.lhs.apply(stats.probability.to.mul)

    Eq << Eq[-1] * Probability(y)


if __name__ == '__main__':
    run()
# created on 2020-12-14
