from util import *


@apply
def apply(imply):
    lhs, rhs = imply.of(Subset)
    function, *limits = lhs.of(Cup)
    return ForAll(Subset(function, rhs).simplify(), *limits)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    x = Symbol.x(shape=(oo,), etype=dtype.complex * n)
    A = Symbol.A(etype=dtype.complex * n)

    Eq << apply(Subset(Cup[i:n](x[i]), A))

    Eq << sets.all_subset.imply.subset.cup.apply(Eq[-1])


if __name__ == '__main__':
    run()

