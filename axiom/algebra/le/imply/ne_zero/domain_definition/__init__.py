from util import *


@apply
def apply(given):
    from axiom.algebra.eq.imply.ne_zero.domain_definition import find_denominator
    lhs, rhs = given.of(LessEqual)
    den = find_denominator(lhs)
    if den is None:
        den = find_denominator(rhs)

    return Unequal(den, 0)


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, c, b, d = Symbol(real=True)
    Eq << apply(a / b + d <= c)

    Eq << sets.le.imply.el.interval.apply(Eq[0])

    Eq << sets.el.imply.any_eq.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(algebra.eq.imply.ne_zero.domain_definition)


if __name__ == '__main__':
    run()

from . import st
# created on 2019-11-17
