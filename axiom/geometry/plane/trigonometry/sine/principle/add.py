from util import *


@apply
def apply(x, y):
    return Equal(sin(x + y), sin(x) * cos(y) + cos(x) * sin(y))


@prove
def prove(Eq):
    from axiom import geometry
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    Eq << apply(x, y)

    Eq << geometry.plane.trigonometry.cosine.principle.add.apply(x + Pi() / 2, y)

    Eq << -Eq[-1]


if __name__ == '__main__':
    run()
