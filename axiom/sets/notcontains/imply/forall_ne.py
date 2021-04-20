from axiom.utility import prove, apply
from sympy import *
from axiom import sets


@apply
def apply(given, reverse=False):
    assert given.is_NotContains    
    e, S = given.args
    
    x = given.generate_free_symbol(**e.type.dict)
    if reverse:
        return ForAll[x:S](Unequal(x, e))
    return ForAll[x:S](Unequal(e, x))


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    
    S = Symbol.S(etype=dtype.integer, given=True)

    Eq << apply(NotContains(x, S))
    
    Eq << ~Eq[1]
    
    Eq << Eq[-1].simplify()
    
    Eq <<= Eq[-1] & Eq[0]
    
if __name__ == '__main__':
    prove()

