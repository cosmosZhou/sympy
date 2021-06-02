from util import *




@apply
def apply(given, wrt=None):
    assert given.is_Subset
    B, A = given.args

    if wrt is None:
        x = B.element_symbol()
    else:
        x = wrt

    return ForAll[x:B](Contains(x, A))


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(complex=True, positive=True)
    A = Symbol.A(etype=dtype.complex * n)
    B = Symbol.B(etype=dtype.complex * n)

    Eq << apply(Subset(B, A))

    x = Eq[1].variable
    Eq << ForAll[x:B](Contains(x, B), plausible=True)

    Eq << Eq[-1].simplify()

    Eq << Eq[-1].this.function.apply(sets.contains.subset.imply.contains, Eq[0])


if __name__ == '__main__':
    run()

