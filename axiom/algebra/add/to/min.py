from util import *


@apply
def apply(self):
    *z, min_xy = self.of(Expr + Min)
    z = Add(*z)

    args = [e + z for e in min_xy]

    return Equal(self, Min(*args))


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(real=True)
    Eq << apply(Min(x, y) - z)

    Eq << Eq[-1].this.rhs.apply(algebra.min.to.piece)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.to.add)

    Eq << Eq[-1].this.lhs.apply(algebra.min.to.piece)


if __name__ == '__main__':
    run()
# created on 2018-08-07
# updated on 2018-08-07
