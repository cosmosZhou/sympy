from util import *

def interval_is_positive(interval):
    if interval.is_Interval:
        if interval.left_open:
            return interval.start >= 0
        else:
            return interval.start > 0

@apply
def apply(given):
    x, R = given.of(Element)
    assert interval_is_positive(R)
    return Element(1 / x, Interval(0, oo, left_open=True))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(hyper_real=True)
    Eq << apply(Element(x, Interval(0, oo, left_open=True)))

    Eq << sets.el.imply.any_eq.apply(Eq[0])

    Eq << algebra.any.imply.any_et.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).simplify()

    Eq << Eq[-1].this.find(Greater).apply(algebra.gt_zero.imply.gt_zero.div)

    Eq << Eq[-1].this.find(Greater).apply(sets.gt_zero.imply.is_positive, simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs, reverse=True, ret=1)

    Eq << algebra.et.imply.cond.apply(Eq[-1], 0)

    
    


if __name__ == '__main__':
    run()
# created on 2021-10-02
# updated on 2022-04-03
