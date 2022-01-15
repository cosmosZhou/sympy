from util import *


@apply
def apply(given):
    x = given.of(Expr >= 0)
    assert x <= 0
    return Equal(x, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(nonpositive=True)
    Eq << apply(x >= 0)

    Eq << LessEqual(x, 0, plausible=True)

    Eq << algebra.le_zero.ge_zero.imply.is_zero.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()

from . import min
# created on 2019-06-16
