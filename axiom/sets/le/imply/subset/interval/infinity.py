from util import *


@apply
def apply(given, left_open=False):
    a, b = given.of(LessEqual)
    return Subset(Interval(b, oo, left_open=left_open), Interval(a, oo, left_open=left_open))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(x <= y)

    t = Symbol(real=True)
    Eq << sets.subset.given.all_el.apply(Eq[1], t)

    Eq << Eq[-1].this.expr.simplify()

    Eq << ~Eq[-1]

    Eq << algebra.any.imply.any_et.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).simplify()

    Eq << Eq[-1].this.expr.apply(algebra.lt.ge.imply.gt.transit)

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2021-02-26
