from util import *


@apply
def apply(given):
    args = given.of(Equal[Mul, 0])

    return Or(*(Equal(arg, 0).simplify() for arg in args))


@prove
def prove(Eq):
    from axiom import algebra

    a, b = Symbol(real=True, given=True)
    Eq << apply(Equal(a * b, 0))

    Eq << ~Eq[-1]

    Eq << Eq[-1].apply(algebra.ne_zero.ne_zero.imply.ne_zero)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2018-03-20
