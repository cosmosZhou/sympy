from util import *


@apply
def apply(given):
    x = given.of(Expr <= 0)
    assert x >= 0
    return Equal(x, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(nonnegative=True)
    Eq << apply(x <= 0)

    Eq << GreaterEqual(x, 0, plausible=True)

    Eq << algebra.ge_zero.le_zero.imply.is_zero.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2018-03-15
