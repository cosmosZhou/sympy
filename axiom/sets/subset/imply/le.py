from axiom.utility import prove, apply
from sympy import *

from axiom import sets


# given: A ⊂ B
# |A| <= |B|
@apply
def apply(given):
    assert given.is_Subset
    A, B = given.args

    return LessEqual(abs(A), abs(B))


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)

    Eq << apply(Subset(A, B))

    Eq << sets.subset.imply.eq.complement.apply(Eq[0])
    
    Eq << ~Eq[1]
    
    Eq << Eq[-1] + Eq[-2].reversed


if __name__ == '__main__':
    prove()

