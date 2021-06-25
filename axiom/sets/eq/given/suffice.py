from util import *




@apply
def apply(eq, wrt=None):
    A, B = eq.of(Equal)
    if wrt is None:
        wrt = eq.generate_var(**A.etype.dict)

    return Suffice(Contains(wrt, A), Contains(wrt, B)), Suffice(Contains(wrt, B), Contains(wrt, A))

@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    A = Symbol.A(etype=dtype.integer * n)
    B = Symbol.B(etype=dtype.integer * n)

    Eq << apply(Equal(A, B), wrt=x)

    Eq << sets.suffice.suffice.imply.eq.apply(Eq[1], Eq[2])


if __name__ == '__main__':
    run()

