from util import *


@apply
def apply(n):
    X = Symbol(integer=True, random=True)
    return Equal(Expectation[X:DieDistribution(n)](X | (X > n / 2)), (n + 1) / 2 + floor(n / 2) / 2)


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    Eq << apply(n)

    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq[-1].this.lhs.ratsimp()


if __name__ == '__main__':
    run()
# created on 2021-08-06
