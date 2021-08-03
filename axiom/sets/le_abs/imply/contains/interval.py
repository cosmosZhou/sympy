from util import *


@apply
def apply(given):
    x, a = given.of(Abs <= Expr)

    return Contains(x, Interval(-a, a))


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, a = Symbol(real=True, given=True)
    Eq << apply(abs(x) <= a)

    Eq << algebra.le_abs.imply.et.apply(Eq[0])
    Eq << sets.contains.given.et.split.interval.apply(Eq[1])


if __name__ == '__main__':
    run()