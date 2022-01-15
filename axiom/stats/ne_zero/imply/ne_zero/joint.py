from util import *


# given: Probability(x | y) != 0
# imply: Probability(x, y) != 0
@apply
def apply(given):
    assert given.is_Unequal
    assert given.lhs.is_Probability
    assert given.rhs.is_zero
    eq = given.lhs.arg
    assert eq.is_Conditioned
    return Unequal(Probability(eq.lhs, eq.rhs), 0)


@prove
def prove(Eq):
    from axiom import stats, algebra

    x, y = Symbol(real=True, random=True)
    Eq << apply(Unequal(Probability(x | y), 0))

    Eq << stats.ne_zero.imply.ne_zero.condition.apply(Eq[0])

    Eq << stats.ne_zero.imply.eq.bayes.apply(Eq[-1], x)

    Eq << algebra.ne_zero.ne_zero.imply.ne_zero.apply(Eq[0], Eq[2])

    Eq << Eq[-1].subs(Eq[-2].reversed)


if __name__ == '__main__':
    run()
# created on 2020-12-11
