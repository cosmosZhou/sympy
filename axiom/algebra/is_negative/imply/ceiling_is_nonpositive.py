from util import *


@apply
def apply(given):
    x = given.of(Expr < 0)

    return LessEqual(Ceiling(x), 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    Eq << apply(x < 0)

    Eq << algebra.is_negative.imply.is_nonpositive.apply(Eq[0])

    Eq << algebra.is_nonpositive.imply.ceiling_is_nonpositive.apply(Eq[-1])


if __name__ == '__main__':
    run()