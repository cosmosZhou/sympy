from util import *


@apply
def apply(given):
    x, domain = given.of(Element)
    a, b = domain.of(Interval)
    if domain.right_open:
        assert b <= 0
    else:
        assert b < 0
        
    return Element(1 / x, Interval(-oo, 0, right_open=True))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(hyper_real=True)
    Eq << apply(Element(x, Interval(-oo, 0, right_open=True)))

    Eq << sets.el.imply.any_eq.apply(Eq[0])

    Eq << algebra.any.imply.any_et.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).simplify()

    Eq << Eq[-1].this.find(Less).apply(algebra.is_negative.imply.is_negative.div)

    Eq << Eq[-1].this.find(Less).apply(sets.is_negative.imply.is_negative_real, simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs, reverse=True)


if __name__ == '__main__':
    run()