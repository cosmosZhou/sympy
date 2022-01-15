from util import *


@apply
def apply(given):
    x, RR = given.of(Element)
    a, b = RR.of(Interval)
    if RR.left_open:
        assert a >= 0
    else:
        assert a > 0
    return x > 0


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(complex=True)
    Eq << apply(Element(x, Interval(0, oo, left_open=True)))

    Eq << sets.el.imply.gt_zero.apply(Eq[0])






if __name__ == '__main__':
    run()
# created on 2020-04-29
