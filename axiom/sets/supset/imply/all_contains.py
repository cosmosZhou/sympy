from util import *


@apply
def apply(imply, var=None):
    A, B = imply.of(Supset)
    if var is None:
        var = B.element_symbol()

    return All[var:B](Contains(var, A))


@prove
def prove(Eq):
    from axiom import sets

    n = Symbol.n(complex=True, positive=True)
    A = Symbol.A(etype=dtype.complex * n, given=True)
    B = Symbol.B(etype=dtype.complex * n, given=True)
    Eq << apply(Supset(B, A))

    Eq << Eq[0].reversed

    Eq << sets.subset.imply.all_contains.apply(Eq[-1])


if __name__ == '__main__':
    run()