from util import *


@apply
def apply(self):
    x = self.of(Abs)
    return Equal(self, abs(-x), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(abs(x - y))

    Eq << Eq[0].this.lhs.apply(algebra.abs.to.piecewise)

    Eq << Eq[-1].this.rhs.apply(algebra.abs.to.piecewise.is_nonpositive)
    Eq << -Eq[-1].this.find(LessEqual)


if __name__ == '__main__':
    run()