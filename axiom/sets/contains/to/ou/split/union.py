from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets


@apply(given=None)
def apply(given, simplify=True):
    assert given.is_Contains
    e, domain = given.args
    
    eqs = [Contains(e, s) for s in axiom.is_Union(domain)]
        
    if simplify:
        eqs = [eq.simplify() for eq in eqs]
        
    return Equivalent(given, Or(*eqs))


@prove
def prove(Eq):
    e = Symbol.e(integer=True, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    C = Symbol.C(etype=dtype.integer, given=True)
    
    Eq << apply(Contains(e, A | B | C))
    
    Eq << Eq[0].this.rhs.simplify()
    

if __name__ == '__main__':
    prove()

