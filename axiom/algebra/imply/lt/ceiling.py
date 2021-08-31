from util import *


@apply
def apply(x):
    return Less(Ceiling(x), x + 1)


@prove(provable=False)
def prove(Eq):
    x = Symbol(real=True)
    Eq << apply(x)
    return
    Eq << Eq[-1].this.lhs.apply(algebra.ceiling.to.mul)

    Eq << Eq[-1] - x

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.frac)


if __name__ == '__main__':
    run()

