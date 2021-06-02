from util import *


@apply
def apply(imply, wrt=None):
    B, A = imply.of(Subset)
    if wrt is None:
        wrt = B.element_symbol()

    return ForAll[wrt:B](Contains(wrt, A))


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(complex=True, positive=True)
    A = Symbol.A(etype=dtype.complex * n, given=True)
    B = Symbol.B(etype=dtype.complex * n, given=True)

    Eq << apply(Subset(B, A))

    Eq << sets.subset.given.is_emptyset.complement.apply(Eq[0])

    Eq << ~Eq[-1]

    Eq << sets.is_nonemptyset.imply.any_contains.st.complement.apply(Eq[-1], simplify=False)

    Eq << algebra.all.any.imply.any_et.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()

