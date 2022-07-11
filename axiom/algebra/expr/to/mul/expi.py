from util import *


@apply
def apply(self):
    return Equal(self, abs(self) * exp(S.ImaginaryUnit * Arg(self)))


@prove
def prove(Eq):
    from axiom import calculus, algebra, geometry

    z = Symbol(complex=True, given=True)
    Eq << apply(z)

    Eq << Eq[0].this.find(Exp).apply(geometry.expi.to.add.Euler)

    Eq << Eq[-1].this.lhs.apply(algebra.expr.to.add.complex)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add)

    Eq << algebra.eq.given.et_eq.complex.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(geometry.re.to.mul.cos)
    Eq << Eq[-1].this.lhs.apply(geometry.im.to.mul.sin)


if __name__ == '__main__':
    run()
# created on 2018-07-26
