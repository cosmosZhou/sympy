from sympy import *
from axiom.utility import prove, apply
from axiom import sets
# given : A \ B = A

# => A & B = EmptySet


@apply
def apply(given):
    assert given.is_Equality
    assert given.lhs.is_Complement
    A, B = given.lhs.args
    assert given.rhs == A

    return Equality(A & B, A.etype.emptySet)




@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    
    Eq << apply(Equality(A - B, A))

    Eq << Eq[0].apply(sets.eq.imply.eq.intersect, B).reversed
    
if __name__ == '__main__':
    prove(__file__)

