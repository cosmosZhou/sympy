from util import *


@apply
def apply(a_less_than_x, x_less_than_b):
    A, X = a_less_than_x.of(Subset)
    _X, B = x_less_than_b.of(Subset)
    if X != _X:
        A, X, _X, B = _X, B, A, X
    assert X == _X
    return Supset(B, A)


@prove
def prove(Eq):
    from axiom import sets
    A, X, B = Symbol(etype=dtype.complex)

    Eq << apply(Subset(A, X), Subset(X, B))

    Eq << sets.subset.subset.imply.subset.transit.apply(Eq[0], Eq[1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
