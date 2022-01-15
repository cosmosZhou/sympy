from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    assert R == Reals - {0}

    return Element(1 / x, Reals)


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(complex=True, given=True)
    Eq << apply(Element(x, Reals - {0}))

    Eq << sets.el.imply.ou.split.union.two.apply(Eq[0], simplify=None)

    Eq << Eq[-1].this.args[0].apply(sets.el.imply.el.inverse.interval, simplify=None)

    Eq << Eq[-1].this.args[1].apply(sets.el.imply.el.inverse.interval, simplify=False)

    Eq << Subset(Eq[-1].rhs, Eq[1].rhs, plausible=True)

    Eq << sets.el.subset.imply.el.apply(Eq[-2], Eq[-1], simplify=None)


if __name__ == '__main__':
    run()
# created on 2020-06-21
