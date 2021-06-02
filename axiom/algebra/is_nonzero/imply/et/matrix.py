from util import *


@apply
def apply(given):
    multiply = given.of(Unequal[ZeroMatrix])
    args = multiply.of(Mul)
    return And(*(Unequal(arg, ZeroMatrix(*arg.shape)).simplify() for arg in args))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(real=True, given=True, shape=(n,))
    b = Symbol.b(real=True, given=True, shape=(n,))
    Eq << apply(Unequal(a * b, ZeroMatrix(n)))

    Eq << algebra.et.given.conds.apply(Eq[-1])

    Eq <<= ~Eq[-1], ~Eq[-2]

    Eq <<= Eq[0].subs(Eq[-1]), Eq[0].subs(Eq[-2])


if __name__ == '__main__':
    run()
