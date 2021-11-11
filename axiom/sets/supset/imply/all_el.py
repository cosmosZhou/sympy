from util import *


@apply
def apply(imply, var=None):
    A, B = imply.of(Supset)
    if var is None:
        var = B.element_symbol()

    return All[var:B](Element(var, A))


@prove
def prove(Eq):
    from axiom import sets

    n = Symbol(complex=True, positive=True)
    A, B = Symbol(etype=dtype.complex * n, given=True)
    Eq << apply(Supset(B, A))

    Eq << Eq[0].reversed

    Eq << sets.subset.imply.all_el.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-06-24
# updated on 2021-06-24
