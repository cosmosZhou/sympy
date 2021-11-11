from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    assert domain in Interval(-1, 0, left_open=True)
    return Equal(Ceiling(x), 0)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(real=True)
    Eq << apply(Element(x, Interval(-1, 0, left_open=True)))

    Eq << sets.el.imply.el.neg.apply(Eq[0])

    Eq << sets.el.imply.floor_is_zero.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.floor.to.mul.ceiling)
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2018-10-22
# updated on 2018-10-22
