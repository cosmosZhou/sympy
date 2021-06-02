from util import *
import axiom



@apply
def apply(given):
    x = given.of(Unequal[0])
    return Greater(abs(x), 0)


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol.a(real=True)

    Eq << apply(Unequal(a, 0))

    Eq << algebra.is_nonzero.imply.is_nonzero.abs.apply(Eq[0])

    Eq << algebra.is_nonzero.imply.is_positive.apply(Eq[-1])


if __name__ == '__main__':
    run()
