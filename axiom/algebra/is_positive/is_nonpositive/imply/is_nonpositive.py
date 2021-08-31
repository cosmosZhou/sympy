from util import *


@apply
def apply(is_positive_x, is_nonpositive_y):
    x = is_positive_x.of(Expr > 0)
    y = is_nonpositive_y.of(Expr <= 0)
    return LessEqual(x * y, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True)

    Eq << apply(x > 0, y <= 0)

    Eq.case0 = Suffice(Equal(y, 0), Eq[-1], plausible=True)

    Eq << Eq.case0.this.apply(algebra.suffice.subs)

    Eq << algebra.cond.imply.suffice.apply(Eq[0], cond=y < 0)

    Eq << algebra.suffice.imply.suffice.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.is_positive.is_negative.imply.is_negative)

    Eq << Eq[-1].this.rhs.apply(algebra.is_negative.imply.is_nonpositive)

    Eq <<= Eq.case0 & Eq[-1]

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[1], Eq[-1])


if __name__ == '__main__':
    run()

