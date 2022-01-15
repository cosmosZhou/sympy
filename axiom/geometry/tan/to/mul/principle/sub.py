from util import *


@apply
def apply(x, y):
    return Equal(tan(x - y), (tan(x) - tan(y)) / (1 + tan(x) * tan(y)))


@prove
def prove(Eq):
    from axiom import geometry
    x, y = Symbol(real=True)

    Eq << apply(x, y)

    Eq << geometry.tan.to.mul.principle.add.apply(x, -y)


if __name__ == '__main__':
    run()
# created on 2020-12-06
