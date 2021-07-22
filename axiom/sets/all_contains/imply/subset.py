from util import *


@apply
def apply(given):
    function, *limits = given.of(All)
    assert len(limits) == 1
    x, A = limits[0]
    _x, B = function.of(Contains)

    assert x == _x
    return Subset(A, B)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    A = Symbol.A(etype=dtype.complex * n)
    B = Symbol.B(etype=dtype.complex * n)

    Eq << apply(All[x:A](Contains(x, B)))

    Eq << Eq[0].this.expr.apply(sets.contains.imply.subset, simplify=False)

    Eq << Eq[-1].apply(sets.all_subset.imply.subset.cup.lhs)


if __name__ == '__main__':
    run()

