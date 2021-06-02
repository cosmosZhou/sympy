from util import *


@apply
def apply(imply):
    x, interval = imply.of(Contains)
    a, b = interval.of(Interval)
    if interval.left_open:
        if interval.right_open:
            return And(x > a, x < b)
        else:
            return And(x > a, x <= b)
    else:
        if interval.right_open:
            return And(x >= a, x < b)
        else:
            return And(x >= a, x <= b)


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(complex=True, given=True)
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    Eq << apply(Contains(x, Interval(a, b, right_open=True)))

    Eq << algebra.et.imply.conds.apply(Eq[-1])

    Eq << sets.lt.imply.contains.interval.apply(Eq[-2], simplify=False)

    Eq << sets.ge.imply.contains.interval.apply(Eq[-2], simplify=False)

    Eq <<= Eq[-2] & Eq[-1]


if __name__ == '__main__':
    run()

