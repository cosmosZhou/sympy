from util import *
import axiom



@apply
def apply(given):
    x = axiom.is_nonnegative(given)
    return x > 0


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)

    Eq << apply(x >= 0)

    Eq << algebra.is_positive.imply.is_nonnegative.apply(Eq[1])


if __name__ == '__main__':
    run()