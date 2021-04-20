from axiom.utility import prove, apply
from sympy import *
from axiom import algebra, sets

# given: A in B
# |B - A| = |B| - |A|
@apply
def apply(given):
    assert given.is_Subset
    A, B = given.args

    return Equal(abs(B - A), abs(B) - abs(A))


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(Subset(A, B, evaluate=False))

    Eq << sets.imply.eq.principle.addition.apply(B - A, B & A)

    Eq << Eq[1].subs(Eq[-1])
    
    Eq << Eq[-1].this.apply(algebra.eq.simplify.terms.common)
    
    Eq << Eq[-1].apply(algebra.is_zero.given.eq)
    
    Eq << sets.subset.imply.eq.intersection.apply(Eq[0])
    
    Eq << Eq[-1].apply(algebra.eq.imply.eq.abs)
    
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    prove()

