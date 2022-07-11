from util import *


@apply
def apply(given):
    x, a = given.of(Abs <= Expr)

    return Element(x, Interval(-a, a))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(abs(x) <= a)

    Eq << sets.el_interval.imply.et.apply(Eq[1])

    Eq << algebra.le.ge.imply.le.abs.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2021-01-06
