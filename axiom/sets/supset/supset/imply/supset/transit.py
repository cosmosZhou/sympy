from util import *


@apply
def apply(a_less_than_x, x_less_than_b):
    X, A = a_less_than_x.of(Supset)
    B, _X = x_less_than_b.of(Supset)
    if X != _X:
        A, X, _X, B = _X, B, A, X
    assert X == _X
    return Supset(B, A)


@prove
def prove(Eq):
    from axiom import sets
    A, X, B = Symbol(etype=dtype.complex)

    Eq << apply(Supset(X, A), Supset(B, X))

    Eq << Eq[0].reversed

    Eq << sets.subset.supset.imply.supset.transit.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2021-07-09
