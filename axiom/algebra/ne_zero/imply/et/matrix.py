from util import *


@apply
def apply(given, index=-1):
    args = given.of(Unequal[Mul, ZeroMatrix])
    lhs = Mul(*args[:index])
    rhs = Mul(*args[index:])

    return Unequal(lhs, ZeroMatrix(*lhs.shape)).simplify(), Unequal(rhs, ZeroMatrix(*rhs.shape)).simplify()


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    a, b = Symbol(real=True, given=True, shape=(n,))
    Eq << apply(Unequal(a * b, ZeroMatrix(n)))



    Eq <<= ~Eq[-1], ~Eq[-2]

    Eq <<= Eq[0].subs(Eq[-1]), Eq[0].subs(Eq[-2])


if __name__ == '__main__':
    run()
# created on 2018-01-26
