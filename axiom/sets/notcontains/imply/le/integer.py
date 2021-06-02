from util import *


@apply
def apply(given):
    assert given.is_NotContains
    n, interval = given.args
    a, _n = interval.of(Range)
    assert n == _n - 1
    return LessEqual(n, a - 1)


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True, given=True)
    a = Symbol.a(integer=True, given=True)

    Eq << apply(NotContains(n, Range(a, n + 1)))

    Eq << ~Eq[-1]

    Eq << algebra.gt.imply.ge.strengthen.apply(Eq[-1])

    Eq << sets.ge.imply.contains.range.apply(Eq[-1], simplify=False)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

