from util import *


@apply
def apply(given):
    x, b = given.of(LessEqual)
    domain = x.domain
    _b, a = domain.of(Interval)
    assert not domain.left_open
    assert b == _b
    
    return Equal(x, b)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True, given=True)
    x = Symbol.x(domain=Interval(b, a), given=True)
    Eq << apply(x <= b)

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()