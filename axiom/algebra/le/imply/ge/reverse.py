from util import *


@apply
def apply(ge):
    x, a = ge.of(LessEqual)
    return GreaterEqual(a, x)


@prove
def prove(Eq):
    x, a = Symbol(real=True, given=True)
    Eq << apply(x <= a)

    Eq << ~Eq[1]

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2019-05-23
# updated on 2019-05-23
