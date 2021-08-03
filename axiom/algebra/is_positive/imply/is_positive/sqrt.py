from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)
    return Greater(sqrt(x), 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True, given=True)
    Eq << apply(Greater(x, 0))

    Eq << algebra.is_positive.imply.is_nonnegative.apply(Eq[0])

    Eq << algebra.is_nonnegative.imply.is_nonnegative.sqrt.apply(Eq[-1])

    Eq << algebra.is_positive.imply.is_nonzero.apply(Eq[0])

    Eq << algebra.is_nonzero.imply.is_nonzero.sqrt.apply(Eq[-1])
    Eq << algebra.is_nonzero.is_nonnegative.imply.is_positive.apply(Eq[-1], Eq[-3])


if __name__ == '__main__':
    run()