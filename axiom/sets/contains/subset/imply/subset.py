from util import *


# given: A in B
# => {A} subset B
@apply
def apply(*given):
    contains, subset = given
    if contains.is_Subset:
        subset, contains = given

    x, S = contains.of(Contains)
    s, _S = subset.of(Subset)
    assert S == _S

    return Subset(s | {x}, S)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,), given=True)
    A = Symbol.A(etype=dtype.complex * n)
    B = Symbol.B(etype=dtype.complex * n, given=True)
    Eq << apply(Contains(x, A), Subset(B, A))

    Eq << sets.contains.imply.subset.apply(Eq[0])

    Eq << sets.subset.subset.imply.subset.union.apply(Eq[-1], Eq[1])

if __name__ == '__main__':
    run()

