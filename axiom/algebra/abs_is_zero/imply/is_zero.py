from util import *


@apply
def apply(given):
    x = given.of(Equal[Abs, 0])
    return Equal(x, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True, given=True)
    Eq << apply(Equal(abs(x), 0))

    Eq << ~Eq[1]

    Eq << algebra.is_nonzero.imply.is_positive.abs.apply(Eq[-1])
    Eq <<= Eq[-1] & Eq[0]
    


if __name__ == '__main__':
    run()