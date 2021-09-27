from util import *


@apply
def apply(contains, subset):
    x, A = contains.of(Element)
    _A, B = subset.of(Subset)
    assert A == _A
    return Element(x, B)


@prove
def prove(Eq):
    from axiom import sets

    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,), given=True)
    A, B = Symbol(etype=dtype.complex * n, given=True)
    Eq << apply(Element(x, A), Subset(A, B))

    Eq << sets.el.imply.el.relax.apply(Eq[0], B)

    Eq << sets.subset.imply.eq.union.apply(Eq[1])

    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    run()

