from util import *


@apply
def apply(*given):
    subset_ab, subset_xy = given
    a, b = subset_ab.of(Supset)
    x, y = subset_xy.of(Supset)

    return Supset(a | x, b | y)


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    X = Symbol.X(etype=dtype.integer)
    Y = Symbol.Y(etype=dtype.integer)

    Eq << apply(Supset(A, B), Supset(X, Y))

    Eq <<= Eq[0].reversed, Eq[1].reversed

    Eq << sets.subset.subset.imply.subset.union.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

