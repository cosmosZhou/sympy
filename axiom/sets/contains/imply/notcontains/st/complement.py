from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains, NotContains
from sympy import Symbol
import axiom


# given: A in B 
# => {A} subset B
@apply
def apply(given):
    assert given.is_Contains
    e, domain = given.args
    S, s = axiom.is_Complement(domain)
    
    return NotContains(e, s)




@prove
def prove(Eq):
    e = Symbol.e(integer=True, given=True)
    s = Symbol.s(etype=dtype.integer, given=True)
    
    S = Symbol.S(etype=dtype.integer, given=True)
    
    Eq << apply(Contains(e, S - s, evaluate=False))
    
    Eq << ~Eq[-1]
    
    Eq <<= Eq[0] & Eq[-1]


if __name__ == '__main__':
    prove()

