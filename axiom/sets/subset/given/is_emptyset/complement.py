
from util import *

# given: B - A = {}
# B in A


@apply
def apply(imply):
    B, A = imply.of(Subset)
    return Equal(Complement(B, A), A.etype.emptySet)


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)

    Eq << apply(Subset(B, A))

    Eq << sets.is_emptyset.imply.subset.complement.apply(Eq[1])


if __name__ == '__main__':
    run()

