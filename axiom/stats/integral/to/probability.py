from util import *


@apply
def apply(self):
    [*eqs], (_x, *_) = self.of(Integral[Probability[And]])

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
    x, y, z = Symbol(real=True, random=True)
    x_ = Symbol('x', real=True)
    Eq << apply(Integral[x_](Probability(x, y, z)))


if __name__ == '__main__':
    run()
# created on 2020-12-07
