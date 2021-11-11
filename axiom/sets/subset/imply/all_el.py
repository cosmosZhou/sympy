from util import *




@apply
def apply(given, wrt=None):
    assert given.is_Subset
    B, A = given.args

    if wrt is None:
        x = B.element_symbol()
    else:
        x = wrt

    return All[x:B](Element(x, A))


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol(complex=True, positive=True)
    A, B = Symbol(etype=dtype.complex * n)

    Eq << apply(Subset(B, A))

    x = Eq[1].variable
    Eq << All[x:B](Element(x, B), plausible=True)

    Eq << Eq[-1].simplify()

    Eq << Eq[-1].this.expr.apply(sets.el.subset.imply.el, Eq[0])


if __name__ == '__main__':
    run()

# created on 2018-03-30
# updated on 2018-03-30
