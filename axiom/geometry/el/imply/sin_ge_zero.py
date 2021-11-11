from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    assert domain in Interval(0, S.Pi)
    return GreaterEqual(sin(x), 0)


@prove
def prove(Eq):
    from axiom import algebra, sets, geometry

    x = Symbol(real=True)
    Eq << apply(Element(x, Interval(0, S.Pi)))

    Eq << algebra.cond.given.et.infer.split.apply(Eq[1], cond=Equal(x, 0))

    Eq << algebra.infer.given.infer.subs.apply(Eq[-2])

    Eq << algebra.cond.given.et.infer.split.apply(Eq[-1], cond=Equal(x, S.Pi))

    Eq << algebra.infer.given.infer.subs.apply(Eq[-2])

    Eq << Eq[-1].this.apply(algebra.infer.flatten)

    Eq << algebra.cond.imply.infer.apply(Eq[0], cond=Eq[-1].lhs)

    Eq << algebra.infer.imply.infer.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.args[:2].apply(sets.ne.el.imply.el, simplify=None)

    Eq << Eq[-1].this.rhs.apply(sets.ne.el.imply.el)

    Eq << Eq[-1].this.rhs.apply(geometry.el.imply.sin_gt_zero)

    Eq << Eq[-1].this.rhs.apply(algebra.gt_zero.imply.ge_zero)


if __name__ == '__main__':
    run()
# created on 2020-11-20
# updated on 2020-11-20
