from sympy import *
from axiom.utility import prove, apply
from axiom import sets
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(A, B):
    return Equal(abs(A | B), abs(A // B) + abs(B))


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    
    Eq << apply(A, B)
    
    C = Symbol.C(A // B)
    
    Eq << Equal(C & B, B.etype.emptySet, plausible=True)
    
    Eq << Eq[-1].subs(C.this.definition)
    
    Eq << sets.is_emptyset.imply.eq.addition_principle.apply(Eq[-1])
    
    Eq << Eq[-1].subs(C.this.definition)


if __name__ == '__main__':
    prove()

