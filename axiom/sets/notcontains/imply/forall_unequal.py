from axiom.utility import prove, apply
from sympy import *
from axiom import sets


@apply(imply=True)
def apply(given, reverse=False):
    assert given.is_NotContains    
    e, S = given.args
    
    x = given.generate_free_symbol(**e.type.dict)
    if reverse:
        return ForAll[x:S](Unequal(x, e))
    return ForAll[x:S](Unequal(e, x))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(integer=True)
    k = Symbol.k(integer=True)
    
    S = Symbol.S(etype=dtype.integer)

    Eq << apply(NotContains(x, S))
    
    Eq << ~Eq[1]
    
    Eq << Eq[-1].simplify()
    
    Eq <<= Eq[-1] & Eq[0]
    
if __name__ == '__main__':
    prove(__file__)

