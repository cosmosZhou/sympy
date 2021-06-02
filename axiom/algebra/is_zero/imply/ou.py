from util import *


@apply
def apply(given):
    multiply = given.of(Equal[0])
    args = multiply.of(Mul)

    return Or(*(Equal(arg, 0).simplify() for arg in args))


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(Equal(a * b, 0))

    Eq << ~Eq[-1]

    Eq << Eq[-1].apply(algebra.is_nonzero.is_nonzero.imply.is_nonzero)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
