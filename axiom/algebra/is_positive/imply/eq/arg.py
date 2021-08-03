from util import *


@apply
def apply(is_positive, z):
    r = is_positive.of(Expr > 0)
    return Equal(Arg(r * z), Arg(z))


@prove
def prove(Eq):
    from axiom import algebra

    z = Symbol(complex=True, given=True)
    r = Symbol(real=True)
    Eq << apply(r > 0, z)

    Eq << algebra.is_positive.imply.any_eq.apply(Eq[0])

    Eq <<= Eq[2] & Eq[1]

    Eq << Eq[-1].this.apply(algebra.cond.any.given.any_et, simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.eq.given.et.subs, swap=True)


if __name__ == '__main__':
    run()