from util import *
import axiom



@apply
def apply(*given):
    a_less_than_x, x_less_than_b = given
    A, X = a_less_than_x.of(Subset)
    _X, B = x_less_than_b.of(Subset)
    if X != _X:
        A, X, _X, B = _X, B, A, X
    assert X == _X
    return Subset(A, B)


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol.A(etype=dtype.complex)
    X = Symbol.X(etype=dtype.complex)
    B = Symbol.B(etype=dtype.complex)

    Eq << apply(Subset(A, X), Subset(X, B))

    Eq << sets.subset.imply.all_contains.apply(Eq[0])

    Eq << Eq[-1].this.function.apply(sets.contains.subset.imply.contains, Eq[1])

    Eq << sets.all_contains.imply.subset.apply(Eq[-1])


if __name__ == '__main__':
    run()
