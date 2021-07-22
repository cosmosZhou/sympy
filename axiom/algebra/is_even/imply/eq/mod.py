from util import *


@apply
def apply(given):
    n = given.of(Equal[Expr % 2, 0])
    return Equal(n // 2, n / 2)


@prove
def prove(Eq):
    from axiom import algebra
#     n = q * d + r
    n = Symbol.n(integer=True)

    Eq << apply(Equal(n % 2, 0))

    Eq << algebra.is_even.imply.any.apply(Eq[0])

    Eq << Eq[-1].this.expr.apply(algebra.eq.imply.eq.div, 2, simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.cond.imply.et.invoke, algebra.eq.imply.eq.floor)

    Eq << Eq[-1].this.expr.apply(algebra.eq.eq.imply.eq.transit)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
