from util import *


@apply
def apply(contains1, contains2):
    assert contains1.is_Element
    assert contains2.is_Element

    x, A = contains1.args
    y, _A = contains2.args
    assert A == _A
    a, b = A.of(Interval)
    return Subset(Interval(x, y, left_open=True), Interval(a, b, right_open=A.right_open, left_open=True))


@prove
def prove(Eq):
    from axiom import sets

    a, b, x, y = Symbol(real=True, given=True)
    S = Interval(a, b, right_open=True)
    Eq << apply(Element(x, S), Element(y, S))

    Eq << sets.el.el.imply.subset.interval.apply(Eq[0], Eq[1])

    Eq << sets.subset.imply.subset.complement.apply(Eq[-1], {x})

    Eq << sets.el.imply.eq.complement.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq.subset = sets.subset.imply.subset.complement.apply(Eq[-1], Eq[-1].rhs.args[0])

    Eq << sets.el_interval.imply.le.apply(Eq[0])

    Eq << sets.le.imply.subset.interval.infinity.apply(Eq[-1], left_open=True)

    Eq << sets.subset.imply.subset.intersect.apply(Eq[-1], Interval(-oo, b, right_open=True))

    Eq << sets.subset.subset.imply.subset.transit.apply(Eq.subset, Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-02-27
