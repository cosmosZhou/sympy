from util import *


@apply
def apply(given):
    x = given.of(Unequal[0])
    return x > 0


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol.a(real=True)
    Eq << apply(Unequal(a, 0))

    Eq << algebra.is_positive.imply.is_nonzero.apply(Eq[1])


if __name__ == '__main__':
    run()
