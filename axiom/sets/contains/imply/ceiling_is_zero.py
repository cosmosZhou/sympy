from util import *


@apply
def apply(contains):
    x, domain = contains.of(Contains)
    assert domain in Interval(-1, 0, left_open=True)
    return Equal(Ceiling(x), 0)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol.x(real=True)
    Eq << apply(Contains(x, Interval(-1, 0, left_open=True)))

    Eq << sets.contains.imply.contains.neg.apply(Eq[0])

    Eq << sets.contains.imply.floor_is_zero.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.floor.to.mul.ceiling)
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()