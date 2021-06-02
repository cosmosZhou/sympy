from util import *


@apply
def apply(imply, right_open=True):
    x, interval = imply.of(Contains)
    a, b = interval.of(Range)
    if right_open:
        return And(x >= a, x < b)
    else:
        return And(x >= a, x <= b - 1)


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(integer=True, given=True)
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    Eq << apply(Contains(x, Range(a, b)), right_open=False)

    Eq << algebra.et.imply.conds.apply(Eq[-1])

    Eq << algebra.le.imply.lt.transit.apply(Eq[-2], upper=b)

    Eq << sets.lt.imply.contains.range.apply(Eq[-1], simplify=False)

    Eq << sets.ge.imply.contains.range.apply(Eq[-3], simplify=False)

    Eq <<= Eq[-2] & Eq[-1]


if __name__ == '__main__':
    run()

