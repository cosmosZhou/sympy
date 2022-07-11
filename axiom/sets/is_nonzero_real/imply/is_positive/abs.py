from util import *


@apply
def apply(given):
    x, RR = given.of(Element)
    assert Element(0, RR) == False
    return Element(abs(x), Interval(0, oo, left_open=True))


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(complex=True)
    Eq << apply(Element(x, Reals - {0}))

    Eq << sets.el_union.imply.ou.apply(Eq[0], simplify=None)

    Eq << Eq[-1].this.args[1].apply(sets.gt_zero.imply.abs_is_positive, simplify=None)

    Eq << Eq[-1].this.args[0].apply(sets.is_negative.imply.is_positive.abs, simplify=None)


if __name__ == '__main__':
    run()
# created on 2020-04-16
