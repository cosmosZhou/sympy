from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebre


@apply
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
    
    Eq << algebre.et.given.cond.apply(Eq[-1])
    
    Eq << Eq[0].apply(sets.contains.imply.contains.having.complement)
    
    Eq << Eq[0].apply(sets.contains.imply.notcontains.having.complement)
    

if __name__ == '__main__':
    prove(__file__)

