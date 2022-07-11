from util import *


def interval_is_negative(interval):
    if interval.is_Interval:
        if interval.right_open:
            return interval.stop <= 0
        else:
            return interval.stop < 0

@apply
def apply(given):
    x, domain = given.of(Element)
    assert interval_is_negative(domain)    
    return Element(1 / x, Interval(-oo, 0, right_open=True))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(hyper_real=True)
    Eq << apply(Element(x, Interval(-oo, 0, right_open=True)))

    Eq << sets.el.imply.any_eq.apply(Eq[0])

    Eq << algebra.any.imply.any_et.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).simplify()

    Eq << Eq[-1].this.find(Less).apply(algebra.lt_zero.imply.lt_zero.div)

    Eq << Eq[-1].this.find(Less).apply(sets.lt_zero.imply.is_negative, simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs, reverse=True)

    


if __name__ == '__main__':
    run()
# created on 2020-04-13
# updated on 2022-04-03
