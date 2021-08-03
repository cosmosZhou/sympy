from util import *


@apply
def apply(self):
    x, y = self.of(Sin[Expr - Expr])
    return Equal(sin(x - y), sin(x) * cos(y) - cos(x) * sin(y))


@prove
def prove(Eq):
    from axiom import geometry

    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(sin(x - y))

    Eq << geometry.sin.to.add.principle.add.apply(sin(x - y))


if __name__ == '__main__':
    run()
