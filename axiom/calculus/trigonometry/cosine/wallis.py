from util import *


@apply
def apply(n):
    n = sympify(n)
    x = Symbol(real=True)
    return Equal(Integral[x:0:pi / 2](cos(x) ** (n - 1)),
                 sqrt(pi) * gamma(n / 2) / (2 * gamma(n / 2 + S.One / 2)))


@prove
def prove(Eq):
    from axiom import calculus, geometry, algebra

    n = Symbol(integer=True, positive=True, given=False)
    Eq << apply(n)

    (x, *_), *_ = Eq[0].lhs.limits
    Eq << Eq[0].subs(n, 1)

    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq[0].subs(n, 2)

    Eq << Eq[-1].this.lhs.doit()

    Eq.induct = Eq[0].subs(n, n + 2)

    Eq << Eq.induct.lhs.this.expand()

    #Integration by parts
    Eq << Eq[-1].this.rhs.apply(calculus.integral.to.add.by_parts, dv=cos(x)) / n

    Eq << Eq[-1].this.lhs.args[1].expr.powsimp()

    Eq << Eq[-1].this.rhs.expr.powsimp()

    Eq << geometry.plane.trigonometry.sine.squared.apply(x)

    Eq << Eq[-2].this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.expr.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.expr.args[0].powsimp()

    Eq << Eq[-1].this.rhs.apply(calculus.integral.to.add)

    Eq << Eq[-1].this.rhs.args[1].simplify()

    Eq << algebra.eq.imply.eq.simple_equation.apply(Eq[-1], -Eq[-1].rhs.args[1])

    Eq << Eq[-1].this.rhs.apply(algebra.mul.cancel, n)

    Eq << Eq[-1].this.rhs.find(Integral).expr.apply(algebra.mul.to.pow.add.exponent)

    Eq << algebra.eq.eq.imply.eq.subs.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq.induct.this.rhs.expand(func=True)

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.eq.eq.infer.imply.eq.induct.apply(Eq[1], Eq[2], Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

# created on 2020-06-30
