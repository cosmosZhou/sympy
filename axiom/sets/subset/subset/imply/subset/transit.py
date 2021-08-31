from util import *



@apply
def apply(a_less_than_x, x_less_than_b):
    A, X = a_less_than_x.of(Subset)
    _X, B = x_less_than_b.of(Subset)
    if X != _X:
        A, X, _X, B = _X, B, A, X
    assert X == _X
    return Subset(A, B)


@prove
def prove(Eq):
    from axiom import sets
    A, X, B = Symbol(etype=dtype.complex)

    Eq << apply(Subset(A, X), Subset(X, B))

    Eq << sets.subset.imply.all_el.apply(Eq[0])

    Eq << Eq[-1].this.expr.apply(sets.el.subset.imply.el, Eq[1])

    Eq << sets.all_el.imply.subset.apply(Eq[-1])


if __name__ == '__main__':
    run()
