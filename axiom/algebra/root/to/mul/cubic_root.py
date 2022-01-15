from util import *


@apply
def apply(self):
    p = self.of((Expr ** 3) ** (S.One / 3))
    return Equal(self, p * exp(-S.ImaginaryUnit * 2 * S.Pi / 3 * Ceiling(3 * Arg(p) / (2 * S.Pi) - S.One / 2)))


@prove
def prove(Eq):
    from axiom import algebra

    p = Symbol(complex=True, given=True)
    Eq << apply((p ** 3) ** (S.One / 3))

    Eq << Eq[0].this.lhs.apply(algebra.root.to.mul.expi.arg)

    Eq << Eq[-1].this.find(Arg).apply(algebra.arg_pow.to.add)

    Eq << Eq[-1].this.find(Exp[~Mul]).apply(algebra.mul.to.add)
    Eq << Eq[-1].this.find(Exp).apply(algebra.exp.to.mul)

    Eq << Eq[-1].this.rhs.apply(algebra.expr.to.mul.expi)


if __name__ == '__main__':
    run()
# created on 2020-03-11
