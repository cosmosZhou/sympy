from util import *




@apply
def apply(eq, wrt=None):
    A, B = eq.of(Equal)
    if wrt is None:
        wrt = eq.generate_var(**A.etype.dict)

    return Suffice(Element(wrt, A), Element(wrt, B)), Suffice(Element(wrt, B), Element(wrt, A))

@prove
def prove(Eq):
    from axiom import sets

    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    A, B = Symbol(etype=dtype.integer * n)
    Eq << apply(Equal(A, B), wrt=x)

    Eq << sets.suffice.suffice.imply.eq.apply(Eq[1], Eq[2])


if __name__ == '__main__':
    run()

