from util import *


@apply
def apply(self):
    *z, max_xy = self.of(Expr + Max)
    z = Add(*z)

    args = [e + z for e in max_xy]

    return Equal(self, Max(*args))


@prove
def prove(Eq):
    from axiom import algebra
    x, y, z = Symbol(real=True)
    Eq << apply(Max(x, y) - z)

    Eq << Eq[-1].this.rhs.apply(algebra.max.to.piece)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.to.add)

    Eq << Eq[-1].this.lhs.apply(algebra.max.to.piece)


if __name__ == '__main__':
    run()
