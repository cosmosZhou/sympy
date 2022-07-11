from util import *


@apply
def apply(given):
    x, a = given.of(Abs <= Expr)

    return Element(x, Interval(-a, a))


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, a = Symbol(real=True, given=True)
    Eq << apply(abs(x) <= a)

    Eq << algebra.abs_le.imply.et.apply(Eq[0])
    Eq << sets.el_interval.given.et.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2021-01-07
