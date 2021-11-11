from util import *


# given: A in B
# => {A} subset B
@apply
def apply(contains, subset):
    if contains.is_Subset:
        subset, contains = given

    x, S = contains.of(Element)
    s, _S = subset.of(Subset)
    assert S == _S

    return Subset(s | {x}, S)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,), given=True)
    A = Symbol(etype=dtype.complex * n)
    B = Symbol(etype=dtype.complex * n, given=True)
    Eq << apply(Element(x, A), Subset(B, A))

    Eq << sets.el.imply.subset.apply(Eq[0])

    Eq << sets.subset.subset.imply.subset.union.apply(Eq[-1], Eq[1])

if __name__ == '__main__':
    run()

# created on 2018-04-21
# updated on 2018-04-21
