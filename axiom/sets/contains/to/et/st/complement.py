from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets, algebra


@apply(given=None)
def apply(given):
    x, complement = axiom.is_Contains(given)
    
    B, A = axiom.is_Complement(complement)
    return Equivalent(given, And(Contains(x, B), NotContains(x, A)))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)

    Eq << apply(Contains(x, B // A))
    
    Eq.sufficient, Eq.necessary = algebra.equivalent.given.sufficient.apply(Eq[-1])
    
    Eq << algebra.sufficient.given.sufficient.split.et.apply(Eq.sufficient)
    
    Eq << Eq[-2].this.lhs.apply(sets.contains.imply.contains.st.complement)
    
    Eq << Eq[-1].this.lhs.apply(sets.contains.imply.notcontains.st.complement)
    
    Eq << Eq.necessary.this.lhs.simplify()
    
    

    
if __name__ == '__main__':
    prove()

