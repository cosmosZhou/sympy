from util import *


@apply
def apply(given):
    lhs, rhs = given.of(GreaterEqual)
    return Or(Greater(lhs, rhs), Equal(lhs, rhs))


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    Eq << apply(x >= y)

    Eq << ~Eq[-1]

    Eq << Eq[-1].simplify()

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()