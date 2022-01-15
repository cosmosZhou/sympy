from util import *


@apply
def apply(imply):
    lhs, rhs = imply.of(Supset)
    assert rhs.is_Cup
    return All(Supset(lhs, rhs.expr).simplify(), *rhs.limits)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    x = Symbol(shape=(oo,), etype=dtype.complex * n)
    A = Symbol(etype=dtype.complex * n)

    Eq << apply(Supset(A, Cup[i:n](x[i])))

    Eq << Eq[1].reversed

    Eq << sets.all_subset.imply.subset.cup.lhs.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2020-09-13
