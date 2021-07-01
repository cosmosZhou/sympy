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
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    z = Symbol.z(real=True)
    Eq << apply(Max(x, y) - z)

    Eq << Eq[-1].this.rhs.apply(algebra.max.to.piecewise)

    Eq << Eq[-1].this.rhs.apply(algebra.piecewise.to.add)

    Eq << Eq[-1].this.lhs.apply(algebra.max.to.piecewise)


if __name__ == '__main__':
    run()
