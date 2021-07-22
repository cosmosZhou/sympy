from util import *


@apply
def apply(x):
    i = S.ImaginaryUnit
    return Equal(E ** (i * x), cos(x) + i * sin(x))


@prove
def prove(Eq):
    from axiom import calculus, algebra, sets, geometry

    x = Symbol.x(real=True)
    Eq << apply(x)

    i = S.ImaginaryUnit
    Eq << calculus.series.maclaurin.exp.apply(i * x)

    n = Eq[-1].rhs.variable
    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add.split, cond=Equal(n % 2, 0))

    Eq << Eq[-1].this.rhs.args[0].limits[0][1].apply(sets.complement.to.conditionset.is_odd)

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.sum.even)

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.sum.odd)

    Eq << Eq[-1].this.rhs.args[0].expr.expand()

    Eq.expand = Eq[-1].this.rhs.args[0].expr.expand()

    Eq << geometry.cos.to.sum.apply(cos(x))

    Eq << geometry.sin.to.sum.apply(sin(x))

    Eq << Eq[-2] + i * Eq[-1]

    Eq << Eq[-1].this.rhs.args[0].args[1].expr.expand()

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.expand, Eq[-1])


if __name__ == '__main__':
    run()

