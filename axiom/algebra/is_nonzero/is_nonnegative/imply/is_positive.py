from util import *


@apply
def apply(is_nonzero, is_nonpositive):    
    x = is_nonzero.of(Unequal[0])
    is_nonpositive.of(x >= 0)    
    return Greater(x, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True, given=True)
    Eq << apply(Unequal(x, 0), GreaterEqual(x, 0))

    Eq << ~Eq[-1]

    Eq << algebra.is_nonpositive.is_nonnegative.imply.is_zero.apply(Eq[-1], Eq[1])

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()