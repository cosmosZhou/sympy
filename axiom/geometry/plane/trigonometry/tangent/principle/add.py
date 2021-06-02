from util import *


@apply
def apply(x, y):
    return Equal(tan(x + y), (tan(x) + tan(y)) / (1 - tan(x) * tan(y)))


@prove
def prove(Eq):
    from axiom import geometry
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    Eq << apply(x, y)

    Eq << Eq[0].this.lhs.astype(Mul)

    Eq << tan(x).this.astype(Mul)

    Eq << tan(y).this.astype(Mul)

    Eq << Eq[1].subs(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.rhs.ratsimp()

    Eq << geometry.plane.trigonometry.sine.principle.add.apply(x, y)

    Eq << geometry.plane.trigonometry.cosine.principle.add.apply(x, y)

    Eq << Eq[-3].subs(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
