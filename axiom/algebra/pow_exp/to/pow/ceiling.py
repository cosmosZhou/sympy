from util import *


@apply
def apply(self):
    x, m = self.of(Pow[Exp[ImaginaryUnit * Expr], Expr ** -1])
    assert m > 0

    return Equal(self, exp(S.ImaginaryUnit * (x - Ceiling(x / (2 * S.Pi) - S.One / 2) * S.Pi * 2) / m))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(exp(S.ImaginaryUnit * x) ** (1 / n))

    Eq << algebra.arg_expi.to.add.ceiling.apply(Arg(Eq[0].lhs.base))

    Eq << Eq[0].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.lhs.apply(algebra.pow_exp.to.exp)


if __name__ == '__main__':
    run()