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

    Eq << algebra.cond.given.et.suffice.split.apply(Eq[1], cond=Equal(x, 0))

    Eq << algebra.suffice.given.suffice.subs.apply(Eq[-2])

    Eq << algebra.cond.given.et.suffice.split.apply(Eq[-1], cond=Equal(x, S.Pi))

    Eq << algebra.suffice.given.suffice.subs.apply(Eq[-2])

    Eq << Eq[-1].this.apply(algebra.suffice.flatten)

    Eq << algebra.cond.imply.suffice.apply(Eq[0], cond=Eq[-1].lhs)

    Eq << algebra.suffice.imply.suffice.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.args[:2].apply(sets.ne.el.imply.el, simplify=None)

    Eq << Eq[-1].this.rhs.apply(sets.ne.el.imply.el)

    Eq << Eq[-1].this.rhs.apply(geometry.el.imply.sin_is_positive)

    Eq << Eq[-1].this.rhs.apply(algebra.is_positive.imply.is_nonnegative)


if __name__ == '__main__':
    run()
