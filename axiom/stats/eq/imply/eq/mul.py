from util import *


# given: x | y = x
# imply: Probability(x, y) = Probability(x) Probability(y)
@apply
def apply(given):
    assert given.is_Equal
    lhs, rhs = given.args

    assert lhs.is_Conditioned

    x, y = lhs.args

    assert x == rhs

    return Equal(Probability(x, y), Probability(x) * Probability(y))


@prove
def prove(Eq):
    from axiom import stats
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)

    given = Equal(x | y, x)

    Eq << apply(given)

    Eq << stats.bayes.corollary.apply(Eq[0].lhs.domain_definition(), var=x)

    Eq << Eq[0].apply(stats.eq.imply.eq.probability, simplify=None)

    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    run()
