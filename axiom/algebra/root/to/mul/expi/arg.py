from util import *


@apply
def apply(self, *, simplify=True):
    z, m = self.of(Pow[Expr, Expr ** -1])
    assert m > 0
    arg = Arg(z)
    if simplify:
        arg = arg.simplify()
    return Equal(self, abs(z) ** (1 / m) * exp(S.ImaginaryUnit * arg / m))


@prove
def prove(Eq):
    from axiom import algebra

    z = Symbol(real=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(z ** (1 / n))

    Eq << Eq[-1].this.lhs.base.apply(algebra.expr.to.mul.expi)

    Eq << Eq[-1].this.lhs.apply(algebra.pow.to.mul.split.base)

    Eq << algebra.eq.given.eq.div.apply(Eq[-1], Eq[-1].lhs.args[0])

    Eq << Eq[-1].this.lhs.apply(algebra.pow_exp.to.exp)

    Eq << Eq[-1].this.lhs.find(Arg).simplify()

    #Eq << Eq[-1].this.lhs.find(Arg).apply(algebra.arg_expi.to.add.ceiling)
    #Eq << Eq[-1].this.find(Ceiling).apply(algebra.ceiling.to.zero.arg)


if __name__ == '__main__':
    run()