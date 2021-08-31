from util import *


@apply
def apply(given):
    function, *limits = given.of(All)
    assert len(limits) == 1
    x, A = limits[0]
    _x, B = function.of(Element)

    assert x == _x
    return Subset(A, B)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    A, B = Symbol(etype=dtype.complex * n)

    Eq << apply(All[x:A](Element(x, B)))

    Eq << Eq[0].this.expr.apply(sets.el.imply.subset, simplify=False)

    Eq << Eq[-1].apply(sets.all_subset.imply.subset.cup.lhs)


if __name__ == '__main__':
    run()

