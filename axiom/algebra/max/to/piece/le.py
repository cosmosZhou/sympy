from util import *


@apply
def apply(self):
    arg, *args = self.of(Max)
    this = self.func(*args)
    rhs = Piecewise((arg, this <= arg), (this, True))

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(Max(x, y))

    Eq << Eq[-1].this.find(LessEqual).reversed
    Eq << Eq[-1].this.lhs.apply(algebra.max.to.piece)


if __name__ == '__main__':
    run()
