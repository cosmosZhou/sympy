from util import *
import axiom



@apply
def apply(given):
    lhs, rhs = given.of(Supset)
    assert rhs.is_Cup
    return ForAll(Supset(lhs, rhs.function, ).simplify(), *rhs.limits)

@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    x = Symbol.x(shape=(oo,), etype=dtype.complex * n)
    A = Symbol.A(etype=dtype.complex * n)

    Eq << apply(Supset(A, Cup[i:n](x[i])))

    Eq << Eq[0].reversed

    Eq << sets.subset.imply.all_subset.split.cup.apply(Eq[-1])

    Eq << Eq[-1].reversed

if __name__ == '__main__':
    run()

