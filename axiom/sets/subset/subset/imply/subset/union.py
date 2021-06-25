from util import *



@apply
def apply(*given):
    subset_ab, subset_xy = given
    a, b = subset_ab.of(Subset)
    x, y = subset_xy.of(Subset)

    return Subset(a | x, b | y)


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    X = Symbol.X(etype=dtype.integer)
    Y = Symbol.Y(etype=dtype.integer)

    Eq << apply(Subset(A, B), Subset(X, Y))

    Eq << sets.subset.imply.subset.relax.apply(Eq[0], Y)

    Eq << sets.subset.imply.subset.relax.apply(Eq[1], B)

    Eq <<= Eq[-1] & Eq[-2]

if __name__ == '__main__':
    run()

