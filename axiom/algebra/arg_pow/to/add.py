from util import *


@apply
def apply(pow):
    z, n = pow.of(Arg[Pow])
    assert n.is_integer and n > 0
    return Equal(pow, Arg(z) * n - Ceiling(Arg(z) * n / (2 * S.Pi) - S.One / 2) * 2 * S.Pi)


@prove
def prove(Eq):
    from axiom import algebra

    z = Symbol(complex=True, given=True)
    n = Symbol(integer=True, given=True, positive=True)
    Eq << apply(Arg(z ** n))

    Eq << Eq[-1].this.lhs.arg.base.apply(algebra.expr.to.mul.expi)

    Eq << Eq[-1].this.lhs.arg.apply(algebra.pow.to.mul.split.base)

    Eq << algebra.cond.given.et.suffice.split.apply(Eq[-1], cond=Unequal(z, 0))

    Eq << algebra.suffice.given.suffice.subs.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(algebra.is_nonzero.imply.abs_is_positive)

    Eq << Eq[-1].this.lhs.apply(algebra.is_positive.imply.pow_is_positive, n)

    Eq << Eq[-1].this.lhs.apply(algebra.is_positive.imply.eq.arg, Eq[-1].find(Exp))

    Eq << algebra.suffice.given.suffice.subs.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.lhs.apply(algebra.arg_expi.to.add.ceiling)


if __name__ == '__main__':
    run()
