from util import *


@apply
def apply(is_nonnegative):
    x = is_nonnegative.of(Expr >= 0)
    assert x in Interval(-1, 1)
    return Equal(asin(x) + asin(sqrt(1 - x ** 2)), S.Pi / 2)


@prove
def prove(Eq):
    from axiom import geometry, algebra, sets

    x = Symbol(domain=Interval(-1, 1))
    Eq << apply(x >= 0)

    Eq << geometry.cos.to.add.principle.add.apply(cos(Eq[1].lhs))

    Eq << algebra.is_nonnegative.imply.eq.abs.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq.any_eq = geometry.cos_is_zero.imply.any.eq.apply(Eq[-1])

    Eq << LessEqual(x, 1, plausible=True)

    Eq << sets.le.ge.imply.contains.interval.apply(Eq[-1], Eq[0])

    Eq <<= geometry.contains.imply.contains.asin.apply(Eq[-1]), sets.contains.imply.contains.sqrt.apply(Eq[-1])

    Eq << geometry.contains.imply.contains.asin.apply(Eq[-1])

    Eq << sets.contains.contains.imply.contains.add.interval.apply(Eq[-1], Eq[-3])

    Eq << algebra.cond.any.imply.any_et.apply(Eq[-1], Eq.any_eq, simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.et.imply.et.invoke, algebra.eq.cond.imply.cond.subs)

    Eq << Eq[-1].this.find(Contains).apply(sets.contains.imply.contains.sub, S.Pi / 2)

    Eq << Eq[-1].this.find(Contains).apply(sets.contains.imply.contains.div.interval, S.Pi)

    #https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()