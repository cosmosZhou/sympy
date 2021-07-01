from util import *


@apply
def apply(*given):
    a_less_than_x, x_less_than_b = given
    A, X = a_less_than_x.of(Subset)
    B, _X = x_less_than_b.of(Supset)
    if X != _X:
        A, X, _X, B = _X, B, A, X
    assert X == _X
    return Supset(B, A)


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol.A(etype=dtype.complex)
    X = Symbol.X(etype=dtype.complex)
    B = Symbol.B(etype=dtype.complex)

    Eq << apply(Subset(A, X), Supset(B, X))

    Eq << Eq[1].reversed

    Eq << sets.subset.subset.imply.subset.transit.apply(Eq[-1], Eq[0])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
