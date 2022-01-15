from util import *


@apply
def apply(self):
    cond, given = self.of(Probability[Conditioned])
    return Equal(self, Probability(cond & given) / Probability(given))


@prove(provable=False)
def prove(Eq):
    x, y = Symbol(real=True, random=True)
    Eq << apply(Probability(x | y))


if __name__ == '__main__':
    run()

from . import guassion
# created on 2020-12-09
