from util import *


@apply
def apply(given):
    x = given.of(Expr <= 0)
    return x < 0


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)

    Eq << apply(x <= 0)

    Eq << algebra.is_negative.imply.is_nonpositive.apply(Eq[1])


if __name__ == '__main__':
    run()
