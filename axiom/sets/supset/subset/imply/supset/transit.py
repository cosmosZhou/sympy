import axiom
from util import *


@apply
def apply(*given):
    a_less_than_x, x_less_than_b = given
    X, A = a_less_than_x.of(Supset)
    _X, B = x_less_than_b.of(Subset)
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

    Eq << apply(Supset(X, A), Subset(X, B))

    Eq << sets.supset.subset.imply.subset.transit.apply(Eq[0], Eq[1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
