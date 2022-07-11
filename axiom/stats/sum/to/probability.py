from util import *


@apply
def apply(self):
    [*eqs], (_x, *_) = self.of(Sum[Probability[And]])

    for i, eq in enumerate(eqs):
        X, x = eq.of(Equal)
        if x == _x:
            break
    else:
        return

    del eqs[i]

    return Equal(self, Probability(And(*eqs)))


@prove(provable=False)
def prove(Eq):
    x, y = Symbol(integer=True, random=True)
    x_ = Symbol('x', integer=True)
    Eq << apply(Sum[x_](Probability(x, y)))


if __name__ == '__main__':
    run()
# created on 2020-12-21
