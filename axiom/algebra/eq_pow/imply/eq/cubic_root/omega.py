from util import *


@apply
def apply(eq_pow):
    A, B = eq_pow.of(Equal)
    from axiom.algebra.eq_pow.eq_ceiling.imply.eq.cubic_root import cubic_root
    A = cubic_root(A)
    B = cubic_root(B)

    #w = -S.One / 2 + sqrt(3) / 2 * S.ImaginaryUnit
    w = exp(S.ImaginaryUnit * 2 * S.Pi / 3)
    d = Ceiling(3 * Arg(A) / (S.Pi * 2) - S.One / 2) - Ceiling(3 * Arg(B) / (S.Pi * 2) - S.One/ 2)
    return Equal(A, B * w ** d)


@prove
def prove(Eq):
    from axiom import algebra

    A, B = Symbol(complex=True, given=True)
    Eq << apply(Equal(A ** 3, B ** 3))

    d = Symbol(Eq[1].find(Ceiling - Ceiling))
    Eq << d.this.definition

    Eq.difference = Eq[-1].this.apply(algebra.eq.transport, rhs=-1).reversed

    Eq << Eq[1].this.lhs.apply(algebra.expr.to.mul.expi)

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.expr.to.mul.expi)

    Eq << Eq[-1].subs(Eq.difference)

    Eq << algebra.eq.imply.eq.pow.apply(Eq[0], exp=S.One / 3)

    Eq << Eq[-1].this.lhs.apply(algebra.root.to.mul.expi.arg)

    Eq << Eq[-1].this.rhs.apply(algebra.root.to.mul.expi.arg)

    Eq << Eq[-1].this.lhs.find(Arg).apply(algebra.arg_pow.to.add)

    Eq << Eq[-1].this.rhs.find(Arg).apply(algebra.arg_pow.to.add)

    Eq << Eq[-1].this.lhs.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.lhs.find(Exp).apply(algebra.exp.to.mul)

    Eq << Eq[-1].this.rhs.find(Exp).apply(algebra.exp.to.mul)

    Eq << Eq[-1].subs(Eq.difference)

    Eq << Eq[-1] / Eq[-1].lhs.args[-1]

    Eq << Eq[-1].this.rhs.args[-1].apply(algebra.expr.to.add.complex)


if __name__ == '__main__':
    run()
# created on 2018-08-28
