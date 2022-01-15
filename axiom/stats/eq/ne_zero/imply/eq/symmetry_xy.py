from util import *


# given: x | y = x
# imply: y | x = y
@apply
def apply(given_equality, unequal):
    assert unequal.is_Unequal
    assert unequal.lhs.is_Probability
    assert unequal.rhs.is_zero

    assert given_equality.is_Equal
    lhs, rhs = given_equality.args
    assert lhs.is_Conditioned
    x, y = lhs.args
    assert x == rhs

    if y.is_Equal:
        y = y.lhs
    assert y.is_random and y.is_symbol
    return Equal(y | x, y)


@prove
def prove(Eq):
    from axiom import stats

    x, y = Symbol(real=True, random=True)
    given = Equal(x | y, x)
    Eq << apply(given, Unequal(Probability(x, y), 0))

    Eq << stats.ne_zero.imply.et.apply(Eq[1])



    Eq << stats.eq.ne_zero.imply.eq.symmetry.apply(Eq[0], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2021-07-16
