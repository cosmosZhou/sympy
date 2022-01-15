from util import *


@apply
def apply(given, reverse=False):
    if reverse:
        given = given.reversed
    (cond, given), rhs = given.of(Equal[Conditioned])
    return Unequal(Probability(given), 0)


@prove(provable=False)
def prove(Eq):
    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Equal(x | y, z))


if __name__ == '__main__':
    run()
# created on 2020-12-07
