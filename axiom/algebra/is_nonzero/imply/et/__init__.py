from util import *


@apply
def apply(given):
    multiply = given.of(Unequal[0])
    args = multiply.of(Mul)
    return And(*(Unequal(arg, 0).simplify() for arg in args))


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(Unequal(a * b, 0))

    Eq << algebra.et.given.conds.apply(Eq[-1])

    Eq <<= ~Eq[-1], ~Eq[-2]

    Eq <<= Eq[0].subs(Eq[-1]), Eq[0].subs(Eq[-2])


if __name__ == '__main__':
    run()
from . import matrix
