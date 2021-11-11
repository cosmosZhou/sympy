from util import *


@apply
def apply(given):
    from axiom.algebra.eq.imply.ne_zero.domain_definition import find_denominator
    num, rhs = given.of(LessEqual[Abs, Expr])
    den = find_denominator(num)

    return Unequal(den, 0)


@prove
def prove(Eq):
    from axiom import algebra

    a, c, b, d = Symbol(real=True)
    Eq << apply(abs(a / b + d) <= c)

    Eq << algebra.abs_le.imply.et.apply(Eq[0])

    Eq << algebra.le.imply.ne_zero.domain_definition.apply(Eq[-2])


if __name__ == '__main__':
    run()
# created on 2019-11-17
# updated on 2019-11-17
