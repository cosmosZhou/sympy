from util import *


@apply
def apply(self):
    x = self.of(Abs)
    return Equal(self, Piecewise((x, x > 0), (0, Equal(x, 0)), (-x, True)))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True)
    Eq << apply(abs(x))

    Eq << Eq[-1].this.rhs.apply(algebra.piece.subs, reverse=True)

    Eq << Eq[-1].this.lhs.apply(algebra.abs.to.piece)


if __name__ == '__main__':
    run()
