from util import *


@apply
def apply(given, reverse=False):
    if reverse:
        given = given.reversed
    (cond, given), rhs = given.of(Equal[Conditioned])
    return Unequal(Probability(given), 0)


@prove(provable=False)
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    z = Symbol.z(real=True, random=True)
    Eq << apply(Equal(x | y, z))


if __name__ == '__main__':
    run()