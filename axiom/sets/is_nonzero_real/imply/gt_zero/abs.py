from util import *


@apply
def apply(given):
    x, RR = given.of(Element)
    assert Element(0, RR) == False
    return Greater(abs(x), 0)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(complex=True)
    Eq << apply(Element(x, Reals - {0}))

    Eq << sets.el_union.imply.ou.apply(Eq[0], simplify=None)

    Eq.is_negative = Infer(Eq[-1].args[0], Eq[1], plausible=True)

    Eq << Eq.is_negative.this.lhs.apply(sets.el.imply.lt_zero)

    Eq << Eq[-1].this.lhs.apply(algebra.lt_zero.imply.ne_zero)

    Eq << Eq[-1].this.lhs.apply(algebra.ne_zero.imply.gt_zero.abs)

    Eq.is_positive = Infer(Eq[2].args[1], Eq[1], plausible=True)

    Eq << Eq.is_positive.this.lhs.apply(sets.el.imply.gt_zero)

    Eq << Eq[-1].this.lhs.apply(algebra.gt_zero.imply.ne_zero)

    Eq << algebra.infer.infer.imply.infer.ou.apply(Eq.is_negative, Eq.is_positive)

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-04-11
