from util import *


@apply
def apply(given):
    x, domain = given.of(Element)
    assert Element(0, domain) == False
    return Element(1 / x, Interval(0, oo, left_open=True) | Interval(-oo, 0, right_open=True))


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(hyper_real=True)
    Eq << apply(Element(x, Interval(0, oo, left_open=True) | Interval(-oo, 0, right_open=True)))

    Eq << sets.el_union.imply.ou.apply(Eq[0])

    Eq << Eq[-1].this.args[0].apply(sets.is_negative.imply.is_negative.div)

    Eq << Eq[-1].this.args[1].apply(sets.gt_zero.imply.is_positive.div)


if __name__ == '__main__':
    run()
# created on 2020-04-14
