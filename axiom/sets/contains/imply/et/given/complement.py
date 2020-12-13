from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains, NotContains
from sympy import Symbol
import axiom
from sympy.logic.boolalg import And
from axiom import sets


@plausible
def apply(given):
    assert given.is_Contains
    e, domain = given.args
    A, B = axiom.is_Complement(domain)
    
    return And(Contains(e, A), NotContains(e, B))


from axiom.utility import check


@check
def prove(Eq):
    e = Symbol.e(integer=True, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    Eq << apply(Contains(e, A - B))
    
    Eq << Eq[-1].split()
    
    Eq << Eq[0].apply(sets.contains.imply.contains.given.complement)
    
    Eq << Eq[0].apply(sets.contains.imply.notcontains.given.complement)
    

if __name__ == '__main__':
    prove(__file__)

