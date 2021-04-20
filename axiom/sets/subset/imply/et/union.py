from axiom.utility import prove, apply
from sympy import *
from axiom import algebra, sets


# given: A in B
# A | B = B
@apply
def apply(given):
    assert given.is_Subset
    A, B = given.args

    return given & Equal(A | B, B)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    subset = Subset(A, B)

    Eq << apply(subset)
    
    Eq << algebra.et.given.cond.apply(Eq[-1])
    
    Eq << sets.subset.imply.eq.union.apply(Eq[0])

if __name__ == '__main__':
    prove()

