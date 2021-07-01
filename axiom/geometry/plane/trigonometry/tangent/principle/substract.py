from util import *


@apply
def apply(x, y):
    return Equal(tan(x - y), (tan(x) - tan(y)) / (1 + tan(x) * tan(y)))


@prove
def prove(Eq):
    from axiom import geometry
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    Eq << apply(x, y)

    Eq << geometry.plane.trigonometry.tangent.principle.add.apply(x, -y)


if __name__ == '__main__':
    run()
