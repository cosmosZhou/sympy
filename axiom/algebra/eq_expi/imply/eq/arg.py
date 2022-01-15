from util import *


@apply
def apply(self):
    x, z = self.of(Equal[Exp[ImaginaryUnit * Expr]])
    return Equal(x, Arg(z) + Ceiling(x / (S.Pi * 2) - S.One / 2) * S.Pi * 2)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    z = Symbol(complex=True)
    Eq << apply(Equal(z, exp(x * S.ImaginaryUnit)))

    Eq << Eq[1].subs(Eq[0])

    Eq << Eq[-1].this.find(Arg).apply(algebra.arg_expi.to.add.ceiling)


if __name__ == '__main__':
    run()
# created on 2019-04-22
