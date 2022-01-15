from util import *


@apply
def apply(given):
    n = given.of(Equal[Expr % 2, 1])
    return Equal(n // 2, (n - 1) / 2)


@prove
def prove(Eq):
    from axiom import algebra

    #n = q * d + r
    n = Symbol(integer=True)
    Eq << apply(Equal(n % 2, 1))

    Eq << algebra.is_odd.imply.any.apply(Eq[0])

    Eq << Eq[-1].this.expr.apply(algebra.eq.imply.eq.div, 2, simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.imply.eq.floor, ret=0)

    Eq << Eq[-1].this.expr.args[0] - S.One / 2

    Eq << Eq[-1].this.expr.apply(algebra.eq.eq.imply.eq.transit)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-10-12
