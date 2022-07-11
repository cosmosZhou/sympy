from util import *


@apply
def apply(imply):
    lhs, rhs = imply.of(Subset)
    function, *limits = lhs.of(Cup)
    return All(Subset(function, rhs).simplify(), *limits)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    x = Symbol(shape=(oo,), etype=dtype.complex * n)
    A = Symbol(etype=dtype.complex * n)

    Eq << apply(Subset(Cup[i:n](x[i]), A))

    Eq << sets.all_subset.imply.subset.cup.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-09-13
