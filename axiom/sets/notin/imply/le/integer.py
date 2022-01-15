from util import *


@apply
def apply(given):
    assert given.is_NotElement
    n, interval = given.args
    a, _n = interval.of(Range)
    assert n == _n - 1
    return LessEqual(n, a - 1)


@prove
def prove(Eq):
    from axiom import algebra, sets

    n, a = Symbol(integer=True, given=True)
    Eq << apply(NotElement(n, Range(a, n + 1)))

    Eq << ~Eq[-1]

    Eq << algebra.gt.imply.ge.strengthen.apply(Eq[-1])

    Eq << sets.ge.imply.el.range.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2021-06-06
