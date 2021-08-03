from util import *


@apply
def apply(self):
    z = self.of(Re)
    
    return Equal(self, abs(z) * cos(Arg(z)))


@prove
def prove(Eq):
    from axiom import geometry, algebra

    z = Symbol(complex=True, given=True)
    Eq << apply(Re(z))

    Eq << Eq[0].this.find(cos).apply(geometry.cos_arg.to.mul)

    Eq << Eq[-1].this.rhs.apply(algebra.mul_piecewise.to.piecewise)
    Eq << Eq[-1].this.find(Abs).apply(algebra.abs.to.sqrt)


if __name__ == '__main__':
    run()