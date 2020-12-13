from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains, NotContains
from sympy import Symbol


# given: A in B 
# => {A} subset B
@plausible
def apply(given, S):
    assert given.is_Contains
    e, s = given.args
    
    return NotContains(e, S - s)


from axiom.utility import check


@check
def prove(Eq):
    e = Symbol.e(integer=True, given=True)
    s = Symbol.s(etype=dtype.integer, given=True)
    
    S = Symbol.S(etype=dtype.integer, given=True)
    
    Eq << apply(Contains(e, s, evaluate=False), S)
    
    Eq << ~Eq[-1]
    
    Eq <<= Eq[0] & Eq[-1]


if __name__ == '__main__':
    prove(__file__)

