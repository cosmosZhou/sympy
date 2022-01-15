from util import *


@apply
def apply(given):
    (num, den), rhs = given.of(Less[Expr / Expr, Expr])

    return Unequal(den, 0)


@prove
def prove(Eq):
    from axiom import sets, algebra
    a, c, b = Symbol(real=True)
    Eq << apply(a / b < c)

    Eq << sets.lt.imply.el.interval.apply(Eq[0])

    Eq << sets.el.imply.any_eq.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(algebra.eq.imply.ne_zero.domain_definition)


if __name__ == '__main__':
    run()
# created on 2020-01-03
