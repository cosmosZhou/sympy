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
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)

    Eq << apply(Unequal(Probability(x | y), 0))

    Eq << Eq[0].domain_definition()

    Eq << stats.bayes.corollary.apply(Eq[-1], var=x)

    Eq << algebra.is_nonzero.is_nonzero.imply.is_nonzero.apply(Eq[0], Eq[2])

    Eq << Eq[-1].subs(Eq[-2].reversed)


if __name__ == '__main__':
    run()
