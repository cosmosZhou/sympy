from util import *


@apply
def apply(imply, right_open=True):
    x, interval = imply.of(Element)
    a, b = interval.of(Range)
    if right_open:
        return x >= a, x < b
    else:
        return x >= a, x <= b - 1


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, a, b = Symbol(integer=True, given=True)
    Eq << apply(Element(x, Range(a, b)), right_open=False)

    Eq << algebra.le.imply.lt.relax.apply(Eq[-1], upper=b)

    Eq << sets.lt.imply.el.range.apply(Eq[-1])

    Eq << sets.ge.imply.el.range.apply(Eq[1])

    Eq <<= Eq[-2] & Eq[-1]


if __name__ == '__main__':
    run()

# created on 2018-03-01
