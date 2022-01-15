from util import *


@apply
def apply(self):
    z = self.of(Cos[Arg])
    x = Re(z)
    y = Im(z)
    r = sqrt(x ** 2 + y ** 2)
    return Equal(self, Piecewise((1, Equal(z, 0)), (x / r, True)))


@prove
def prove(Eq):
    from axiom import algebra, geometry

    z = Symbol(complex=True, given=True)
    Eq << apply(cos(Arg(z)))

    Eq << algebra.expr.to.add.complex.apply(z)

    Eq << algebra.eq.imply.eq.arg.apply(Eq[1])

    Eq << Eq[-1].this.rhs.apply(geometry.arg.to.piece.acos)

    Eq << geometry.eq.imply.eq.cos.apply(Eq[-1])

    Eq << Eq[0].this.find(Equal).apply(algebra.is_zero.to.et.is_zero)


if __name__ == '__main__':
    run()
# created on 2018-06-12
