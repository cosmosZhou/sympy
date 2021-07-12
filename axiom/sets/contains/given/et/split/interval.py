from util import *


@apply
def apply(imply):
    x, interval = imply.of(Contains)
    a, b = interval.of(Interval)
    if interval.left_open:
        if interval.right_open:
            return x > a, x < b
        else:
            return x > a, x <= b
    else:
        if interval.right_open:
            return x >= a, x < b
        else:
            return x >= a, x <= b


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol.x(complex=True, given=True)
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    Eq << apply(Contains(x, Interval(a, b, right_open=True)))

    Eq <<= sets.lt.imply.contains.interval.apply(Eq[-1]), sets.ge.imply.contains.interval.apply(Eq[-2])

    Eq <<= Eq[-2] & Eq[-1]


if __name__ == '__main__':
    run()

