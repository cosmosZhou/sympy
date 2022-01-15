from util import *


@apply
def apply(given):
    x, RR = given.of(Element)
    a, b = RR.of(Interval)
    if RR.right_open:
        assert b <= 0
    else:
        assert b < 0
    return Element(abs(x), -RR)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(complex=True)
    Eq << apply(Element(x, Interval(-oo, 0, right_open=True)))

    Eq << sets.el.imply.lt_zero.apply(Eq[0])

    Eq << algebra.lt_zero.imply.eq.abs.apply(Eq[-1])

    Eq << Eq[1].subs(Eq[-1])

    Eq << sets.el.imply.el.neg.apply(Eq[0], simplify=None)


if __name__ == '__main__':
    run()
# created on 2020-04-15
