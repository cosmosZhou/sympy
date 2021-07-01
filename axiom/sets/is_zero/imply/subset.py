from util import *


@apply
def apply(given):
    B, A = given.of(Equal[Abs[Complement], 0])
    return Subset(B, A)


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)

#     Eq << apply(Equal(abs(B // A), 0))
    Eq << apply(Equal(0, abs(B // A)))

    Eq << sets.is_zero.imply.is_emptyset.apply(Eq[0])

    Eq << sets.is_emptyset.imply.subset.complement.apply(Eq[-1])


if __name__ == '__main__':
    run()

