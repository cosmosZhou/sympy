from util import *


@apply
def apply(self):
    (X, x), (_x, *_) = self.of(Sum[Probability[Equal[Symbol, Symbol]]])
    assert x == _x

    return Equal(self, 1)


@prove(provable=False)
def prove(Eq):
    x = Symbol(integer=True, random=True)
    x_ = Symbol('x', integer=True)
    Eq << apply(Sum[x_](Probability(x)))


if __name__ == '__main__':
    run()
from . import conditioned
# created on 2021-07-19
