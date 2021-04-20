
from axiom.utility import prove, apply


from sympy import *
from axiom import sets
# given: B - A = {} 
# B in A


@apply
def apply(given):
    assert given.is_Equal
    abs_A_minus_B, zero = given.args
    if not zero.is_Zero:
        zero, abs_A_minus_B = given.args
    assert zero.is_Zero
    assert abs_A_minus_B.is_Abs
    A_minus_B = abs_A_minus_B.arg
    assert A_minus_B.is_Complement
    
    B, A = A_minus_B.args

    return Subset(B, A)




@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)

    Eq << apply(Equal(abs(B - A), 0))
    
    Eq << sets.is_zero.imply.is_emptyset.apply(Eq[0])
    
    Eq << sets.is_emptyset.imply.subset.complement.apply(Eq[-1])

if __name__ == '__main__':
    prove()

