from util import *


@apply
def apply(is_zero, contains):
    x = is_zero.of(Equal[Cos, 0])
    _x, domain = contains.of(Element)
    assert _x == x
    assert domain in Interval(0, S.Pi)
    assert S.Pi / 2 in domain
    return Equal(x, S.Pi / 2)


@prove
def prove(Eq):
    from axiom import sets, geometry

    x = Symbol(real=True, given=True)
    Eq << apply(Equal(cos(x), 0), Element(x, Interval(0, S.Pi)))

    Eq.gt = Greater(x, S.Pi / 2, plausible=True)

    Eq << sets.gt.el.imply.el.intersect.apply(Eq.gt, Eq[1])

    Eq << geometry.el.imply.cos_lt_zero.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]

    Eq.lt = Less(x, S.Pi / 2, plausible=True)

    Eq << sets.lt.el.imply.el.intersect.apply(Eq.lt, Eq[1])

    Eq << geometry.el.imply.cos_gt_zero.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]
    Eq <<= ~Eq.gt & ~Eq.lt

    #https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
# created on 2018-06-23
