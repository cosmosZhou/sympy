from util import *


@apply
def apply(is_nonpositive):
    x = is_nonpositive.of(Expr <= 0)
    assert x in Interval(-1, 1)
    return Equal(asin(sqrt(1 - x ** 2)) - asin(x), S.Pi / 2)


@prove
def prove(Eq):
    from axiom import geometry, algebra, sets

    x = Symbol(domain=Interval(-1, 1))
    Eq << apply(x <= 0)

    Eq << geometry.cos.to.add.principle.apply(cos(Eq[1].lhs))

    Eq << algebra.le_zero.imply.eq.abs.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << geometry.cos_is_zero.imply.any.eq.apply(Eq[-1])

    Eq << -Eq[-1].this.expr

    Eq << Eq[-1].this.apply(algebra.any.limits.negate.infinity)

    Eq << algebra.any.imply.any.limits.subs.offset.apply(Eq[-1], 1)

    Eq.any_eq = Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << GreaterEqual(x, -1, plausible=True)

    Eq << sets.ge.le.imply.el.interval.apply(Eq[-1], Eq[0])

    Eq <<= geometry.el.imply.el.asin.apply(Eq[-1]), sets.el.imply.el.sqrt.max.apply(Eq[-1])

    Eq <<= sets.el.imply.el.neg.apply(Eq[-2]), geometry.el.imply.el.asin.apply(Eq[-1])

    Eq << sets.el.el.imply.el.add.interval.apply(Eq[-1], Eq[-2])

    Eq << algebra.cond.any.imply.any_et.apply(Eq[-1], Eq.any_eq, simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs, ret=0)

    Eq << Eq[-1].this.find(Element).apply(sets.el.imply.el.sub, S.Pi / 2)

    Eq << Eq[-1].this.find(Element).apply(sets.el.imply.el.div.interval, S.Pi)

    #https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
# created on 2018-07-13
