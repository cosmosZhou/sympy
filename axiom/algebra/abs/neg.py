from util import *


@apply
def apply(self):
    x = self.of(Abs)
    return Equal(self, abs(-x), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(abs(x - y))

    Eq << Eq[0].this.lhs.apply(algebra.abs.to.piece)

    Eq << Eq[-1].this.rhs.apply(algebra.abs.to.piece.le_zero)
    Eq << -Eq[-1].this.find(LessEqual)


if __name__ == '__main__':
    run()
# created on 2018-01-19
# updated on 2018-01-19
