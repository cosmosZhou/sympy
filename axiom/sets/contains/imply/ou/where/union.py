from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets


@apply
def apply(given, complement=None):
    assert given.is_Contains
    e, domain = given.args
    A, B = axiom.is_Union(domain)
    
    if complement:
        return Or(Contains(e, A), Contains(e, B - A))
    return Or(Contains(e, A), Contains(e, B))


@prove
def prove(Eq):
    e = Symbol.e(integer=True, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    Eq << apply(Contains(e, A | B), complement=True)
    
    Eq << ~Eq[-1]

    Eq << Eq[-1].apply(sets.notcontains.notcontains.imply.notcontains.union)
    
    Eq <<= Eq[-1] & Eq[0]
    

if __name__ == '__main__':
    prove(__file__)

