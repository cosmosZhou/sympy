from util import *


@apply
def apply(given):
    abs_x, a = given.of(Less)
    x = abs_x.of(Expr ** 2)
    return Less(x, sqrt(a)), Less(-sqrt(a), x)


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(integer=True, given=True)
    Eq << apply(x ** 2 < a ** 2)

    Eq << algebra.lt.gt.imply.lt.abs.apply(Eq[-2], Eq[-1].reversed)

    Eq << algebra.lt.imply.lt.square.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-01-15
# updated on 2020-01-15
