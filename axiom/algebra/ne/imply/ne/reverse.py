from util import *


@apply
def apply(ne):
    a, b = ne.of(Unequal)
    return Unequal(b, a)


@prove
def prove(Eq):
    b = Symbol.b(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    Eq << apply(Unequal(a, b))

    Eq << ~Eq[1]

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()