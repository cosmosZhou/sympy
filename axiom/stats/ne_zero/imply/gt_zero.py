from util import *


# given: x | y = x
# imply: y | x = y
@apply
def apply(given):
    assert given.is_Unequal
    assert given.lhs.is_Probability
    assert given.rhs.is_zero

    return Greater(given.lhs, 0)


@prove
def prove(Eq):
    x = Symbol(real=True, random=True)

    Eq << apply(Unequal(Probability(x), 0))

    Eq << GreaterEqual(Probability(x), 0, plausible=True)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2020-12-08
