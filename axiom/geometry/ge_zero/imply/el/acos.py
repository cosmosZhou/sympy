from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    a, b = domain.of(Interval)
    assert a in Interval(-1, 1)
    assert b in Interval(-1, 1, right_open=True)
    assert domain.left_open and domain.right_open
    return Element(acos(x), Interval(acos(b), acos(a), left_open=domain.right_open, right_open=domain.left_open))


@prove
def prove(Eq):
    from axiom import sets, geometry

    x = Symbol(real=True)
    a = Symbol(domain=Interval(-1, 1))
    b = Symbol(domain=Interval(-1, 1, right_open=True))
    Eq << apply(Element(x, Interval(a, b, right_open=True, left_open=True)))

    Eq << sets.el_interval.given.et.apply(Eq[1])

    Eq.gt, Eq.lt = sets.el_interval.imply.et.apply(Eq[0])

    Eq << Element(a, Interval(-1, 1), plausible=True)

    Eq << Element(b, Interval(-1, 1), plausible=True)

    Eq << sets.el.el.imply.subset.interval.right_open.apply(Eq[-2], Eq[-1])

    Eq << Subset(Interval(a, b, left_open=True, right_open=True), Interval(a, b, right_open=True), plausible=True)

    Eq << sets.subset.subset.imply.subset.transit.apply(Eq[-1], Eq[-2])

    Eq << sets.el.subset.imply.el.apply(Eq[0], Eq[-1])

    Eq << Element(b, Interval(-1, 1, right_open=True), plausible=True)

    Eq << geometry.lt.el.el.imply.gt.acos.apply(Eq.lt, Eq[-2], Eq[-1])

    Eq << geometry.lt.el.el.imply.gt.acos.apply(Eq.gt.reversed, Eq[4], Eq[-2]).reversed


if __name__ == '__main__':
    run()
# created on 2020-12-01
