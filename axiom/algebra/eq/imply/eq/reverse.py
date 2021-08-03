from util import *


@apply
def apply(eq):
    a, b = eq.of(Equal)
    return Equal(b, a)


@prove
def prove(Eq):
    b = Symbol.b(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    Eq << apply(Equal(a, b))

    Eq << ~Eq[1]

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()