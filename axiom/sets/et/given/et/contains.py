from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets, algebra


# i ∈ [d + j; n) & j ∈ [a; -d + n)
@apply
def apply(given):
    equal, contains = axiom.is_And(given)
         
    a, A = axiom.is_Contains(contains)
    _A, union_B_aset = axiom.is_Equal(equal)
    
    if A != _A:
        _A, union_B_aset = union_B_aset, _A
        
    B, aset = axiom.is_Union(union_B_aset)
    if aset != a.set:
        B, aset = aset, B    

    return Equal(A // aset, B // aset) & Contains(a, A) 


@prove
def prove(Eq):
    a = Symbol.a(integer=True)
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    
    Eq << apply(Contains(a, A) & Equal(B | a.set, A))
    
    Eq << Eq[1].apply(sets.contains.eq.imply.eq)
    
    Eq << Eq[-1].reversed
    
    Eq << algebra.et.imply.cond.apply(Eq[1])
    
    Eq << algebra.et.given.cond.apply(Eq[0])
    
    

    
if __name__ == '__main__':
    prove()

