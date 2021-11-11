from util import *


@apply
def apply(given):
    assert given.is_Unequal
    assert given.lhs.is_Probability
    assert given.rhs.is_zero
    eq = given.lhs.arg
    assert eq.is_Conditioned
    return Unequal(Probability(eq.rhs), 0)


@prove(provable=False)
def prove(Eq):
    x, y = Symbol(real=True, random=True)
    Eq << apply(Unequal(Probability(x | y), 0))


if __name__ == '__main__':
    run()
# created on 2020-12-10
# updated on 2020-12-10
