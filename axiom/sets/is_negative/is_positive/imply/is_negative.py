from util import *


@apply
def apply(b_is_negative, a_is_positive):
    a, aR = a_is_positive.of(Element)
    b, bR = b_is_negative.of(Element)
    from axiom.sets.is_positive.imply.is_positive.div import interval_is_positive
    assert interval_is_positive(aR)
    from axiom.sets.is_negative.imply.is_negative.div import interval_is_negative
    assert interval_is_negative(bR)
    return Element(a * b, Interval(-oo, 0, right_open=True))


@prove
def prove(Eq):
    from axiom import sets

    x, y = Symbol(hyper_real=True)
    Eq << apply(Element(y, Interval(-oo, 0, right_open=True)), Element(x, Interval(0, oo, left_open=True)))

    Eq << sets.el.imply.el.neg.apply(Eq[0])

    Eq << sets.is_positive.is_positive.imply.is_positive.apply(Eq[-1], Eq[1])

    Eq << sets.el.imply.el.neg.apply(Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2022-04-03
