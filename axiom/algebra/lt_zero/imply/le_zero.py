from util import *


@apply
def apply(given):
    x = given.of(Expr < 0)
    return x <= 0


@prove
def prove(Eq):
    x = Symbol(real=True, given=True)

    Eq << apply(x < 0)

    Eq << ~Eq[1]

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2018-02-07
