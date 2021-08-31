from util import *


@apply
def apply(given, bound):
    lhs, rhs = given.of(Greater)

    assert bound >= rhs

    return Greater(lhs, bound)


@prove
def prove(Eq):
    x, y = Symbol(real=True, given=True)

    Eq << apply(Greater(x, y), y + 1)

    Eq << ~Eq[0]

#     Eq <<= Eq[1] & Eq[-1]

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()

