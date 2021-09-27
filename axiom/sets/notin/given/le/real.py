from util import *


@apply
def apply(given):
    n, interval = given.of(NotElement)
    a, b = interval.of(Interval)
    assert b > a
    return LessEqual(n, a)


@prove
def prove(Eq):
    x, a = Symbol(real=True, given=True)
    Eq << apply(NotElement(x, Interval(a, oo, left_open=True)))

    Eq << ~Eq[0]

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()

