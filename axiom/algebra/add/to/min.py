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

    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    z = Symbol.z(real=True)
    Eq << apply(Min(x, y) - z)

    Eq << Eq[-1].this.rhs.apply(algebra.min.to.piecewise)

    Eq << Eq[-1].this.rhs.apply(algebra.piecewise.to.add)

    Eq << Eq[-1].this.lhs.apply(algebra.min.to.piecewise)


if __name__ == '__main__':
    run()
