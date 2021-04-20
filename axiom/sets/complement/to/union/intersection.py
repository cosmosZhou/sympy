from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom
# A \ (B \ C) = (A \ B) | (A & B & C)


@apply
def apply(complement, evaluate=False):
    A, BC = axiom.is_Complement(complement)    
    B, C = axiom.is_Complement(BC)
    return Equal(complement, Union(A // B, A & B & C, evaluate=evaluate))


@prove
def prove(Eq):
    B = Symbol.B(etype=dtype.integer)
    A = Symbol.A(etype=dtype.integer)
    C = Symbol.C(etype=dtype.integer)

    Eq << apply(A // (B // C))
    
    D = Symbol.D(A // B)
    I = Symbol.I(A & B)
    Eq << Equal(A, D | I, plausible=True)
    
    Eq << Eq[-1].this.rhs.args[0].definition
    
    Eq << Eq[-1].this.find(Complement, Complement).args[1].definition
    
    Eq << Eq[0].lhs.this.subs(Eq[1])
    
    Eq << Eq[-1].this.rhs.apply(sets.complement.to.union.st.union)
    
    Eq << Eq[-1].this.rhs.subs(D.this.definition)
    
    Eq << (C & I).this.args[1].definition
    
    Eq << Eq[0].rhs.this.subs(Eq[-1].reversed)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-3], Eq[-1])

    
if __name__ == '__main__':
    prove()

