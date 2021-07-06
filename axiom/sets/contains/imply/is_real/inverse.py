from util import *


@apply
def apply(given):
    x, R = given.of(Contains)
    R == Reals - {0}
    assert x.is_complex
    
    return Contains(1 / x, Reals)


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol.x(complex=True, given=True)
    Eq << apply(Contains(x, Reals - {0}))

    Eq << sets.contains.imply.ou.split.union.two.apply(Eq[0], simplify=None)

    Eq << Eq[-1].this.args[0].apply(sets.contains.imply.contains.interval.inverse)

    Eq << Eq[-1].this.args[1].apply(sets.contains.imply.contains.interval.inverse)

    Eq << Subset(Eq[-1].rhs, Eq[1].rhs, plausible=True)
    Eq << sets.contains.subset.imply.contains.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()