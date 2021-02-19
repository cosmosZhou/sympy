from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets


@apply
def apply(imply):
    assert imply.is_Contains
    e, domain = imply.args
    A, B = axiom.is_Union(domain)
    
    return Or(Contains(e, A), Contains(e, B))


@prove
def prove(Eq):
    e = Symbol.e(integer=True, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    Eq << apply(Contains(e, A | B))    
    
    Eq << ~Eq[0]
    
    Eq << sets.notcontains.imply.et.where.union.apply(Eq[-1], simplify=None)
    
    Eq << ~Eq[-1]
        

if __name__ == '__main__':
    prove(__file__)

