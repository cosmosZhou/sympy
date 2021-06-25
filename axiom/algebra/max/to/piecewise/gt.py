from util import *


@apply
def apply(self):
    arg, *args = self.of(Max)
    this = self.func(*args)
    rhs = Piecewise((arg, arg > this), (this, True))

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(Max(x, y))

    Eq << Eq[-1].this.find(Greater).reversed
    Eq << Eq[-1].this.lhs.apply(algebra.max.to.piecewise.lt)


if __name__ == '__main__':
    run()