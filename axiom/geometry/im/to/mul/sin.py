from util import *


@apply
def apply(self):
    z = self.of(Im)
    
    return Equal(self, abs(z) * sin(Arg(z)))


@prove
def prove(Eq):
    from axiom import geometry, algebra

    z = Symbol(complex=True, given=True)
    Eq << apply(Im(z))

    Eq << Eq[0].this.find(sin).apply(geometry.sin_arg.to.mul)

    Eq << Eq[-1].this.rhs.apply(algebra.mul_piecewise.to.piecewise)

    Eq << Eq[-1].this.find(Abs).apply(algebra.abs.to.sqrt)


if __name__ == '__main__':
    run()