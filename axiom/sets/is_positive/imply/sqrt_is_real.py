from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)
    return Contains(sqrt(x), Reals)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol(real=True, given=True)
    Eq << apply(x > 0)

    Eq << algebra.is_positive.imply.is_nonnegative.apply(Eq[0])
    Eq << sets.is_nonnegative.imply.sqrt_is_real.apply(Eq[-1])
    

    

    

    


if __name__ == '__main__':
    run()