from util import *


@apply
def apply(given):
    x, b = given.of(GreaterEqual)
    domain = x.domain
    a, b = domain.of(Interval)
    assert not domain.right_open

    return Equal(x, b)


@prove
def prove(Eq):
    a = Symbol(real=True)
    b = Symbol(real=True, given=True)
    x = Symbol(domain=Interval(a, b), given=True)

    Eq << apply(x >= b)

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

