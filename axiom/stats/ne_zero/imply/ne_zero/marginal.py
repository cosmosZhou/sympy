from util import *


# given: Probability(x | y) != 0
# imply: Probability(x) != 0
@apply
def apply(given):
    assert given.is_Unequal
    assert given.lhs.is_Probability
    assert given.rhs.is_zero
    eq = given.lhs.arg
    assert eq.is_Conditioned
    return Unequal(Probability(eq.lhs), 0)


@prove
def prove(Eq):
    from axiom import stats

    x, y = Symbol(real=True, random=True)
    Eq << apply(Unequal(Probability(x | y), 0))

    Eq << stats.ne_zero.imply.ne_zero.joint.apply(Eq[0])

    Eq << stats.ne_zero.imply.et.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-07-22
