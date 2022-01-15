from util import *


@apply
def apply(self):
    x = self.of(Arg[Exp[ImaginaryUnit * Expr]])
    return Equal(self, x + Floor(-x / (S.Pi * 2) + S.One / 2) * S.Pi * 2)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    Eq << apply(Arg(exp(S.ImaginaryUnit * x)))

    Eq << Eq[-1].this.lhs.apply(algebra.arg_expi.to.add.ceiling) / 2

    Eq << Eq[-1].this.rhs.apply(algebra.floor.to.mul.ceiling)


if __name__ == '__main__':
    run()
# created on 2019-03-01
