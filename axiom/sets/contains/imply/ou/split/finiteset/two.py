from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets


@apply
def apply(given):
    assert given.is_Contains
    e, finiteset = given.args
    a, b = axiom.is_FiniteSet(finiteset, size=2)
    
    return Or(Equal(e, a), Equal(e, b))


@prove
def prove(Eq):
    e = Symbol.e(integer=True, given=True)
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    Eq << apply(Contains(e, {a, b}))
    
    Eq << ~Eq[-1]
    
    Eq << Eq[-1].apply(sets.ne.ne.imply.notcontains, simplify=False)
    
    Eq <<= Eq[-1] & Eq[0]
    

if __name__ == '__main__':
    prove()

