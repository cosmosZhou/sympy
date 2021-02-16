from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets


@apply(imply=True)
def apply(given):
    assert given.is_Contains
    e, domain = given.args
    A, B = axiom.is_Complement(domain)
    
    return And(Contains(e, A), NotContains(e, B))


@prove
def prove(Eq):
    e = Symbol.e(integer=True, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    Eq << apply(Contains(e, A - B))
    
    Eq << Eq[-1].split()
    
    Eq << Eq[0].apply(sets.contains.imply.contains.where.complement)
    
    Eq << Eq[0].apply(sets.contains.imply.notcontains.where.complement)
    

if __name__ == '__main__':
    prove(__file__)

