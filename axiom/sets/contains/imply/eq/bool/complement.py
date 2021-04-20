from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets


@apply
def apply(given):
    e, domain = axiom.is_Contains(given)
    _, s = axiom.is_Complement(domain)
    return Equal(Bool(NotContains(e, s)), 1)


@prove
def prove(Eq):
    e = Symbol.e(integer=True)
    s = Symbol.s(etype=dtype.integer)
    S = Symbol.S(etype=dtype.integer)
    Eq << apply(Contains(e, S - s))
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << sets.contains.imply.notcontains.st.complement.apply(Eq[0])
    

if __name__ == '__main__':
    prove()

