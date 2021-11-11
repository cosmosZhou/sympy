from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    [*_] = R.of(Interval[NegativeInfinity, 0])

    assert R.right_open
    assert x.is_complex
    return Less(x, 0)


@prove
def prove(Eq):
    x = Symbol(complex=True, given=True)
    Eq << apply(Element(x, Interval(-oo, 0, right_open=True)))

    Eq << ~Eq[1]

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2020-04-10
# updated on 2020-04-10
