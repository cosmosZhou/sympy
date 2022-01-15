from util import *


@apply
def apply(x, y):
    return Equal(tan(x + y), (tan(x) + tan(y)) / (1 - tan(x) * tan(y)))


@prove
def prove(Eq):
    from axiom import geometry

    x, y = Symbol(real=True)
    Eq << apply(x, y)

    Eq << Eq[0].this.lhs.apply(geometry.tan.to.mul)

    Eq << tan(x).this.apply(geometry.tan.to.mul)

    Eq << tan(y).this.apply(geometry.tan.to.mul)

    Eq << Eq[1].subs(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.rhs.ratsimp()

    Eq << Eq[-1].this.find(Sin[Add]).apply(geometry.sin.to.add.principle)

    Eq << Eq[-1].this.find(Cos[Add]).apply(geometry.cos.to.add.principle)




if __name__ == '__main__':
    run()
# created on 2020-12-06
