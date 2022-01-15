from util import *


@apply
def apply(imply):
    x, interval = imply.of(Element)
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

    x = Symbol(complex=True, given=True)
    a, b = Symbol(integer=True, given=True)
    Eq << apply(Element(x, Interval(a, b, right_open=True)))

    Eq <<= sets.lt.imply.el.interval.apply(Eq[-1]), sets.ge.imply.el.interval.apply(Eq[-2])

    Eq <<= Eq[-2] & Eq[-1]


if __name__ == '__main__':
    run()

# created on 2018-04-07
